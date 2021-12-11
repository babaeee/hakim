# تاکتیک ها

در هر لحظه از اثبات، چندین هدف برای اثبات کردن وجود دارد و ما با چنین چیزی مواجه هستیم:

```
 H0: gozare
 H1: farz
 H2: a = b
--------------------------------------------(1/2)
    gozare1
--------------------------------------------(2/2)
    gozare1
```

هر هدف را به صورت یک فریم نگهداری می کنیم که ساختار زیر را دارد:

```rust
pub struct Frame {
    pub goal: TermRef,
    pub hyps: im::HashMap<String, TermRef>,
    pub engine: Engine,
}
```

هر تاکتیک، یک فریم به عنوان ورودی می گیرد و لیستی از فریم ها را خروجی می دهد. تاکتیک ها روی فریم
فعال (هدف شماره یک) اجرا می شوند. بعد از اجرای یک تاکتیک، فریمی که تاکتیک رویش اجرا شده حذف می شود
و فریم هایی که تاکتیک خروجی داد به ابتدای لیست فریم ها اضافه می شوند (مثل یک استک)

برای مثال تاکتیک اپلای، یک قضیه شرطی را روی حکم اعمال می کند و به کاربر اجازه می دهد که به جای
اثبات حکم، گزاره هایی را ثابت کند که طبق این قضیه شرطی حکم را نتیجه می دهند. پس تاکتیک اپلای
باید به ازای هر پیش شرط یک فریم جدید بسازد و در صورتی که کاربر توانست همه آن ها را حل کند، آن گاه
می توان فریم فعلی را حل شده در نظر گرفت.

اگر یک تاکتیک کاملا یک هدف را حل می کند، می تواند یک لیست خالی برگرداند. مثل تاکتیک رینگ:

```rust
pub fn ring(frame: Frame) -> Result<Vec<Frame>> {
    let goal = frame.goal;
    let [op1, op2, _] = get_eq_params(&goal).ok_or(BadGoal("ring only work on equality"))?;
    let d1 = canonical(ArithTree::from(op1));
    let d2 = canonical(ArithTree::from(op2));
    if d1 == d2 {
        Ok(vec![])
    } else {
        Err(CanNotSolve("ring"))
    }
}
```

و اگر یک تاکتیک نیاز دارد که تغییری در همین فریم فعلی اعمال کند، می تواند فریمی که ورودی گرفته را
تغییر داده و سپس به عنوان یک لیست تک عضوی خروجی دهد تا کاربر هدف تغییر داده شده را ثابت کند. مثل
تاکتیک بازنویسی:

```rust
pub fn rewrite(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
            // ^^^
    // ......
    frame.goal = if is_reverse {
        replace_term(goal, op2, op1)
    } else {
        replace_term(goal, op1, op2)
    };
    Ok(vec![frame])
}
```

به طور معمول تاکتیک ها را در یک ماژول در
`interactive::tactic`
قرار می دهیم. سپس آن ها را در تابع
`interactive::Frame::run_tactic`
صدا می کنیم:

```rust
pub fn run_tactic(&self, line: &str) -> Result<Vec<Self>, tactic::Error> {    
    // .............
    match name.as_str() {
        "intros" => intros(frame, parts),
        "rewrite" => rewrite(frame, parts),
        // >> here <<
        "apply" => apply(frame, parts),
        // ........
    }
}
```

سپس یک تست برای استفاده از این تاکتیک در
`interactive::tests`
اضافه می کنیم.

