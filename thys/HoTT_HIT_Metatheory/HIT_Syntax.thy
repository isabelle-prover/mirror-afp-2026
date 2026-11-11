theory HIT_Syntax
  imports Main
begin

section \<open>A structural HIT calculus\<close>

text \<open>
  This stand-alone Isabelle/HOL session fixes a small type theory whose
  \<^emph>\<open>only\<close> type formers are function spaces and higher inductive types drawn
  from a signature environment.  The calculus is finitary, one-dimensional
  and nondependent: signatures contain finite lists of point and path
  constructors, constructor arguments have fixed higher-inductive types, and
  eliminators have a constant motive.  The development studies syntax,
  reduction, typing, signature well-formedness, free dimension support,
  boundary coherence, substitution, subject reduction, progress, multi-step
  type safety, strong normalization, confluence, and canonical forms.

  Two design decisions make the treatment uniform.

    \<^item> Higher inductive types are not built in one at a time.  A signature
      lists point constructors and path constructors, each with a list of
      argument specifications, and each path constructor with two endpoints
      expressed over its own arguments.  Ordinary inductive types are the
      signatures with no path constructors, so the natural numbers, the unit
      type and the empty type are instances of the same schema.

    \<^item> Path constructors are \<^emph>\<open>cubical-style\<close>: a path constructor applied
      to its arguments takes a further dimension argument, and the eliminator
      computes on it judgmentally.  The endpoints are not separate rules but
      the result of substituting the two constant dimensions, so the boundary
      of a path constructor is part of dimension substitution rather than of
      reduction.  This is a small syntax with dimension variables, not a
      formalization of cubical type theory or its Kan operations.

  Dimension variables are natural numbers.  Index \<open>0\<close> is reserved: it is the
  dimension bound by the path methods of an eliminator.  Ambient dimension
  contexts therefore consist of strictly positive indices, and no shifting is
  ever required.
\<close>

subsection \<open>Types, dimensions, endpoints, and terms\<close>

datatype ty =
    Fun ty ty
  | Hit nat

text \<open>
  An argument of a constructor is either a parameter, whose type is one of
  the higher inductive types of the signature environment, or a recursive
  occurrence of the type being described.  Restricting parameters to higher
  inductive types is no loss for the usual examples: ordinary inductive types
  are themselves instances of the schema.  What it excludes is infinitary
  constructors, whose arguments are functions into the type being defined.
\<close>

datatype argspec =
    Par nat
  | Rec

text \<open>
  An endpoint of a path constructor is a point-constructor term over the
  arguments of that path constructor.
\<close>

datatype endpt =
    EArg nat
  | ECon nat "endpt list"

datatype dim =
    D0
  | D1
  | DVar nat

record hsig =
  pcons :: "argspec list list"
  lcons :: "argspec list list"
  lends :: "(endpt \<times> endpt) list"

datatype tm =
    Var nat
  | Lam ty tm
  | App tm tm
  | PCon nat nat "tm list"
  | LCon nat nat "tm list" dim
  | HElim nat ty "tm list" "tm list" tm

type_synonym sigenv = "nat \<Rightarrow> hsig"

subsection \<open>Instantiating an endpoint\<close>

primrec instE :: "nat \<Rightarrow> tm list \<Rightarrow> endpt \<Rightarrow> tm" where
  "instE h as (EArg j) = as ! j"
| "instE h as (ECon k es) = PCon h k (map (instE h as) es)"

definition lhsOf :: "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> tm" where
  "lhsOf S h k as = instE h as (fst (lends (S h) ! k))"

definition rhsOf :: "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> tm" where
  "rhsOf S h k as = instE h as (snd (lends (S h) ! k))"

text \<open>
  The smart constructor for path constructors.  Applying a path constructor
  at a constant dimension \<^emph>\<open>is\<close> the corresponding endpoint; there is no
  separate boundary rule.
\<close>

definition mkL :: "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> dim \<Rightarrow> tm" where
  "mkL S h k as d =
    (case d of
       D0 \<Rightarrow> lhsOf S h k as
     | D1 \<Rightarrow> rhsOf S h k as
     | DVar j \<Rightarrow> LCon h k as (DVar j))"

lemma mkL_simps [simp]:
  "mkL S h k as D0 = lhsOf S h k as"
  "mkL S h k as D1 = rhsOf S h k as"
  "mkL S h k as (DVar j) = LCon h k as (DVar j)"
  by (simp_all add: mkL_def)

subsection \<open>Substitution for term variables\<close>

primrec lift :: "nat \<Rightarrow> tm \<Rightarrow> tm" where
  "lift n (Var i) = (if i < n then Var i else Var (Suc i))"
| "lift n (Lam A t) = Lam A (lift (Suc n) t)"
| "lift n (App t u) = App (lift n t) (lift n u)"
| "lift n (PCon h k as) = PCon h k (map (lift n) as)"
| "lift n (LCon h k as d) = LCon h k (map (lift n) as) d"
| "lift n (HElim h C pms lms t) =
    HElim h C (map (lift n) pms) (map (lift n) lms) (lift n t)"

primrec subst :: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
  "subst n s (Var i) =
    (if i < n then Var i else if i = n then s else Var (i - 1))"
| "subst n s (Lam A t) = Lam A (subst (Suc n) (lift 0 s) t)"
| "subst n s (App t u) = App (subst n s t) (subst n s u)"
| "subst n s (PCon h k as) = PCon h k (map (subst n s) as)"
| "subst n s (LCon h k as d) = LCon h k (map (subst n s) as) d"
| "subst n s (HElim h C pms lms t) =
    HElim h C (map (subst n s) pms) (map (subst n s) lms) (subst n s t)"

subsection \<open>Substitution for dimension variables\<close>

primrec dsubstD :: "nat \<Rightarrow> dim \<Rightarrow> dim \<Rightarrow> dim" where
  "dsubstD n d D0 = D0"
| "dsubstD n d D1 = D1"
| "dsubstD n d (DVar j) = (if j = n then d else DVar j)"

primrec dsubst :: "sigenv \<Rightarrow> nat \<Rightarrow> dim \<Rightarrow> tm \<Rightarrow> tm" where
  "dsubst S n d (Var i) = Var i"
| "dsubst S n d (Lam A t) = Lam A (dsubst S n d t)"
| "dsubst S n d (App t u) = App (dsubst S n d t) (dsubst S n d u)"
| "dsubst S n d (PCon h k as) = PCon h k (map (dsubst S n d) as)"
| "dsubst S n d (LCon h k as e) =
    mkL S h k (map (dsubst S n d) as) (dsubstD n d e)"
| "dsubst S n d (HElim h C pms lms t) =
    HElim h C (map (dsubst S n d) pms)
      (if n = 0 then lms else map (dsubst S n d) lms)
      (dsubst S n d t)"

subsection \<open>Iterated application and eliminator arguments\<close>

definition apps :: "tm \<Rightarrow> tm list \<Rightarrow> tm" where
  "apps t xs = foldl App t xs"

lemma apps_Nil [simp]: "apps t [] = t"
  by (simp add: apps_def)

lemma apps_Cons [simp]: "apps t (x # xs) = apps (App t x) xs"
  by (simp add: apps_def)

lemma apps_append: "apps t (xs @ ys) = apps (apps t xs) ys"
  by (simp add: apps_def)

text \<open>
  When an eliminator meets a constructor, every argument is handed to the
  method, and every \<^emph>\<open>recursive\<close> argument is handed over a second time
  together with the value of the eliminator on it.
\<close>

primrec elimArgs ::
  "nat \<Rightarrow> ty \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> argspec list \<Rightarrow> tm list \<Rightarrow> tm list"
where
  "elimArgs h C pms lms [] as = []"
| "elimArgs h C pms lms (s # ss) as =
    (case as of
       [] \<Rightarrow> []
     | a # as' \<Rightarrow>
         (case s of
            Par h' \<Rightarrow> [a]
          | Rec \<Rightarrow> [a, HElim h C pms lms a])
         @ elimArgs h C pms lms ss as')"

lemma elimArgs_Nil_args [simp]: "elimArgs h C pms lms ss [] = []"
  by (induct ss) simp_all

end
