# پارسر

ما برای ورودی گرفتن عبارت ها و نمایش دادن آن ها نیاز به یک پارسر داریم تا عبارت ها را از شکل
آدم فهم به شکل ماشین فهم تبدیل کنیم. در ماژول پارسر علاوه بر پارسر یک زیبا چاپ کن (پرتی پرینتر) هم
وجود دارد که برعکس این کار را انجام می دهد، یعنی عبارت را به یک رشته قابل نمایش تبدیل می کند.

پارسری که در این جا پیاده شده، روش معمولی در طراحی کامپایلر های زبان های برنامه نویسی است.

## لکسر

در مرحله اول، رشته خام ورودی گرفته شده تبدیل به لیستی از توکن ها می شود. تابع زیر این کار را انجام
می دهد:

```rust
parser::tokenizer::tokenize
pub fn tokenize(mut text: &str) -> Result<Vec<Token>, String>
```

در این مرحله هر عدد یا هر اسم و چیز های مشابه گروه بندی می شود تا در مرحله بعدی به جای کار مستقیم
با کاراکتر ها با توکن ها کار کنیم.

## AST

در مرحله بعد، آرایه توکن ها به درخت نحو انتزاعی
(Abstract syntax tree)
تبدیل می شود. درخت نحو ساختار رشته ورودی را به یک درخت تبدیل می کند که هر عبارت یک راس در این درخت
است و هر زیر عبارت یک عبارت، به صورت راس فرزند در درخت در می آید. در مورد
[AST می توانید در ویکی پدیا](https://en.wikipedia.org/wiki/Abstract_syntax_tree)
بخوانید.

تابع زیر وظیفه تبدیل لیست توکن ها به درخت نحو را دارد:

```rust
parser::ast::tokens_to_ast
pub fn tokens_to_ast(mut tokens: &[Token]) -> Result<AstTerm> {
    let ast = tokens.eat_ast()?;
    if tokens.is_empty() {
        Ok(ast)
    } else {
        Err(RemainTokens(tokens.to_vec()))
    }
}
```

نیازمند تکمیل!

## عملگر های دو عملوندی

نیازمند تکمیل!

## تبدیل درخت نحو به عبارت

در نهایت در تابع زیر

```rust
parser::ast::ast_to_term
pub fn ast_to_term(
    ast: AstTerm,
    globals: &im::HashMap<String, TermRef>,
    name_stack: &mut Vec<String>,
    infer_dict: &mut HashMap<String, usize>,
    infer_cnt: &mut usize,
) -> Result<TermRef>
```

ورودی اول، درخت نحوی است که می خواهیم آن را به عبارت تبدیل کنیم. ورودی دوم، اسامی گلوبال (مثلا
چیز هایی که از کتابخانه ها وارد شده اند) است که توسط موتور فراهم می شوند. ورودی سوم، استک اسامی
لوکال (مثل متغیر فورآل یا اکزیستس) است که باید به ایندکس دیبروینه تبدیل شوند. ورودی های بعدی را
در قسمت «جای خالی ها» توضیح می دهیم.

### جای خالی ها

در عبارت ورودی می تواند تعدادی جای خالی وجود داشته باشد مثل
`? < ?x + ?x`
از جای خالی در جستجو، بعضی از تاکتیک ها و ... استفاده می شود. پر کردن جای خالی ها در مرحله پارس مقدور
نیست و نیاز به اطلاعات تایپ ها دارد. به همین دلیل امکان تعریف جای خالی در عبارت وجود دارد. با این حال
جای خالی در عبارت صرفا یک عدد است اما در مرحله پارس یک نام اختیاری دارد. در عبارت جای خالی هایی که شماره
یکسان دارند مساوی هم در نظر گرفته می شوند. در پارسر جای خالی هایی که نام ندارند یکتا در نظر گرفته می شوند
و آن هایی که نام دارند با هم نام هایشان معادل هستند و باید بهشان یک شماره یکتا تخصیص داده شود. 

متغیر
`infer_cnt`
تعداد شماره هایی که تا کنون اختصاص داده ایم را نگه می دارد و برای ساخت یک شماره جدید آن را یک واحد
زیاد می کنیم و مقدار قبلی آن را استفاده می کنیم. در
`infer_dict`
نیز شماره هایی که به نام ها اختصاص دادیم را ذخیره می کنیم.

علاوه بر جای خالی هایی که مستقیم با علامت سوال توسط کاربر وارد می شوند، یک سری جای خالی ضمنی وجود
دارد. مثلا
`eq`
یک تابع سه ورودی است که ورودی اول آن تایپ ورودی های دوم و سوم است. بنابراین ما
`2 = 3`
را به
`eq ? 2 3`
تبدیل می کنیم به امید این که این جای خالی در مراحل بعد تر پر شود. کد این کار را می توانیم ببینیم:

```rust
Eq => {
    let i = *infer_cnt;
    *infer_cnt += 1;
    let w = term_ref!(_ i);
    app_ref!(eq(), w, l, r)
}
```


