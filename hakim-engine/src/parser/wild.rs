use crate::brain::{fill_wild_with_depth, infer::RESERVED_SPACE, Term, TermRef};

#[derive(Default)]
pub struct InferGenerator(pub usize);

impl InferGenerator {
    pub fn generate(&mut self) -> usize {
        let i = self.0;
        self.0 += 1;
        RESERVED_SPACE * i
    }
}

struct Dsu(Vec<usize>);

impl Dsu {
    fn new(n: usize) -> Self {
        Self((0..n).collect())
    }

    fn add_group(&mut self) -> usize {
        let x = self.0.len();
        self.0.push(x);
        x
    }

    fn get(&mut self, a: usize) -> usize {
        if self.0[self.0[a]] != self.0[a] {
            self.0[a] = self.get(self.0[a]);
        }
        self.0[a]
    }

    fn merge(&mut self, a: usize, b: usize) {
        let a = self.get(a);
        let b = self.get(b);
        self.0[a] = b;
    }
}

struct FixWildDfsState {
    dsu: Dsu,
    lca: Vec<usize>,
    group: Vec<usize>,
}

impl FixWildDfsState {
    fn new(n: usize) -> Self {
        let n = RESERVED_SPACE * n;
        Self {
            dsu: Dsu::new(n + 1),
            lca: vec![0; n],
            group: vec![n],
        }
    }

    fn dfs(&mut self, term: &Term) {
        match term {
            Term::Var { .. } | Term::Number { .. } | Term::Axiom { .. } | Term::Universe { .. } => {
            }
            Term::Forall(a) | Term::Fun(a) => {
                self.dfs(&a.var_ty);
                self.group.push(self.dsu.add_group());
                self.dfs(&a.body);
                let g = self.group.pop().unwrap();
                self.dsu.merge(g, *self.group.last().unwrap());
            }
            Term::App { func, op } => {
                self.dfs(func);
                self.dfs(op);
            }
            Term::Wild { index, scope: _ } => {
                let i = *index;
                let g = self.dsu.get(i);
                let level = self
                    .group
                    .iter()
                    .enumerate()
                    .find(|(_, x)| self.dsu.get(**x) == g)
                    .map(|(a, _)| a);
                match level {
                    Some(level) => {
                        self.lca[i] = level;
                    }
                    None => {
                        self.lca[i] = self.group.len() - 1;
                        self.dsu.merge(i, *self.group.last().unwrap());
                    }
                }
            }
        }
    }
}

/// Wilds has an index and a scope, which means they belong to which depth of abstraction
/// and checks if inference is allowed to fill them via some abstract variable or not
pub fn fix_wild_scope(term: TermRef, n: usize) -> TermRef {
    let mut state = FixWildDfsState::new(n);
    state.dfs(&term);
    let lca = state.lca;
    fill_wild_with_depth(
        term,
        &|i, scope, depth| {
            assert_eq!(scope, 0, "scopes should be clean (= 0) before fixing");
            TermRef::new(Term::Wild {
                index: i,
                scope: depth - lca[i],
            })
        },
        0,
    )
}
