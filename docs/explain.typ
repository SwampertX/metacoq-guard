#let yellow(body) = {highlight(body)}
#let red(body) = {highlight(color: red, body)}
#let state(cs, s, rs, ge, le) = {
  grid(columns:(auto, auto),
  align: (right,left),
  column-gutter: 1em,
  row-gutter: 0.8em,
  [call stack:]  , [(#cs)],
  [stack:]       , [(#s)],
  [redex stack:] , [(#rs)],
  [guard env:]   , [(#ge)],
  [loc env:]     , [(#le)],
  )}

= `add`
#table(columns: (auto, auto),
align: start,

[ ```ml
Fixpoint add (m n : nat):
match m with
| O => n
| S m' => add m' (S n)
end.
``` ],

[ $\
  "call stack"  &: []\
  "stack"       &: []\
  "redex stack" &: []\
  "guard env"   &: []\
  "loc env"     &: []\
$ ],

[ ```ml
fun (n : nat) => 
match m with
| O => n
| S m' => add m' (S n)
end.
``` ],

[ $\
  "call stack"  &: ["tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [m, "add"]\
$ ],

[ ```ml
match m with
| O => n
| S m' => add m' (S n)
end.
``` ],

[ $\
  "call stack"  &: ["tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
m (* discriminant *)
``` ],

[ $\
  "call stack"  &: ["tRel", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
n (* 0-th branch *)
``` ],

[ $\
  "call stack"  &: ["tRel", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
fun m' : nat => add m' (S n)
(* 1-st branch *)
``` ],

[ $\
  "call stack"  &: ["tLambda", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
add m' (S n)
``` ],

[ $\
  "call stack"  &: ["tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
S n
``` ],

[ $\
  "call stack"  &: ["tApp", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
n
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
S
``` ],

[ $\
  "call stack"  &: ["tConstruct", "tApp", "tApp", "tCase", "tLambda"]\
  "stack"       &: ["SClosure" n]\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
m'
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
add
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: ["SClosure" m', "SClosure" "(S n)"]\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
(* internal *)
check_is_subterm
  (subterm_specif m')
  (wf_paths nat)
== NeedReduceSubterm {}
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: ["SClosure" m', "SClosure" "(S n)"]\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: [m', n, m, "add"]\
$ ],

[ ```ml
(* internal *)
reduce_if
  (needreduce discriminant ||
   needreduce branches)
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],
)

#pagebreak()
= `add_typo`

#table(columns: (auto, auto),
align: start,

[ 
```ml
Fixpoint add_typo (m n : nat) :=
match m with
| O => n
| S unused => add_typo m (S n)
end.
``` ],

[ $\
  "call stack"  &: []\
  "stack"       &: []\
  "redex stack" &: []\
  "guard env"   &: []\
  "loc env"     &: []\
$ ],

[ ```ml
fun (n : nat) => 
match m with
| O => n
| S unused => add m (S n)
end.
``` ],

[ $\
  "call stack"  &: ["tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [m, "add"]\
$ ],

[ ```ml
match m with
| O => n
| S unused => add m (S n)
end.
``` ],

[ $\
  "call stack"  &: ["tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
m (* discriminant *)
``` ],

[ $\
  "call stack"  &: ["tRel", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
n (* 0-th branch *)
``` ],

[ $\
  "call stack"  &: ["tRel", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
fun unused : nat => add m (S n)
(* 1-st branch *)
``` ],

[ $\
  "call stack"  &: ["tLambda", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Bound"{1}, "Large"]\
  "loc env"     &: [n, m, "add"]\
$ ],

[ ```ml
add m (S n)
``` ],

[ $\
  "call stack"  &: ["tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: ["unused", n, m, "add"]\
$ ],

[ ```ml
S n
``` ],

[ $\
  "call stack"  &: ["tApp", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: ["unused", n, m, "add"]\
$ ],

[ ```ml
m
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: ["unused", n, m, "add"]\
$ ],

[ ```ml
add
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: ["SClosure" m, "SClosure" "(S n)"]\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: ["unused", n, m, "add"]\
$ ],

[ ```ml
(* internal *)
check_is_subterm
  (subterm_specif m)
  (wf_paths nat)
== NotSubterm
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tCase", "tLambda"]\
  "stack"       &: ["SClosure" m, "SClosure" "(S n)"]\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Strict", "Bound"{1}, "Large"]\
  "loc env"     &: ["unused", n, m, "add"]\
$ ],
)

#pagebreak()
= `f`

#table(columns: (auto, auto),
align: start,

[```ml
Fixpoint f (x : bool) :=
  let _ := f x in true.
``` ],

[ $\
  "call stack"  &: []\
  "stack"       &: []\
  "redex stack" &: []\
  "guard env"   &: []\
  "loc env"     &: []\
$ ],

[```ml
Fixpoint f (x : bool) :=
  let b := f x in true.
``` ],

[ $\
  "call stack"  &: []\
  "stack"       &: []\
  "redex stack" &: []\
  "guard env"   &: []\
  "loc env"     &: []\
$ ],

[```ml
let b := f x in true.
``` ],

[ $\
  "call stack"  &: ["tLetIn"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],

[```ml
f x (* bound term *)
``` ],

[ $\
  "call stack"  &: ["tApp", "tLetIn"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],

[```ml
x
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tLetIn"]\
  "stack"       &: []\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],

[```ml
f
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tLetIn"]\
  "stack"       &: ["SClosure" x]\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],

[```ml
f
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tLetIn"]\
  "stack"       &: ["SClosure" x]\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],

[ ```ml
(* internal *)
check_is_subterm
  (subterm_specif x)
  (wf_paths bool)
== NotSubterm
``` ],

[ $\
  "call stack"  &: ["tRel", "tApp", "tLetIn"]\
  "stack"       &: ["SClosure" x]\
  "redex stack" &: ["NoNeed", "NoNeed", "NoNeed"]\
  "guard env"   &: ["Large"]\
  "loc env"     &: [x,f]\
$ ],
)