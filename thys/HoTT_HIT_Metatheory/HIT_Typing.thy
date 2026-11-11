theory HIT_Typing
  imports HIT_Reduction
begin

section \<open>Typing\<close>

text \<open>
  A judgment carries an ambient dimension context, a set of dimension
  variables, and an ordinary typing context.  The reserved index \<open>0\<close> never
  belongs to an ambient dimension context: it is bound by the path methods of
  an eliminator, and the typing rule for the eliminator is the only place
  where it enters scope.
\<close>

primrec argTy :: "nat \<Rightarrow> argspec \<Rightarrow> ty" where
  "argTy h (Par h') = Hit h'"
| "argTy h Rec = Hit h"

text \<open>
  A method for a constructor consumes the arguments of that constructor, and
  in addition, for every recursive argument, the value of the eliminator on
  it.  This is exactly the list produced by \<^const>\<open>elimArgs\<close>.
\<close>

primrec methodTy :: "nat \<Rightarrow> ty \<Rightarrow> argspec list \<Rightarrow> ty" where
  "methodTy h C [] = C"
| "methodTy h C (s # ss) =
    (case s of
       Par h' \<Rightarrow> Fun (Hit h') (methodTy h C ss)
     | Rec \<Rightarrow> Fun (Hit h) (Fun C (methodTy h C ss)))"

inductive wt :: "sigenv \<Rightarrow> nat set \<Rightarrow> ty list \<Rightarrow> tm \<Rightarrow> ty \<Rightarrow> bool"
  for S :: sigenv
where
  wtVar:
    "i < length G \<Longrightarrow> wt S D G (Var i) (G ! i)"
| wtLam:
    "wt S D (A # G) t B \<Longrightarrow> wt S D G (Lam A t) (Fun A B)"
| wtApp:
    "wt S D G t (Fun A B) \<Longrightarrow> wt S D G u A \<Longrightarrow> wt S D G (App t u) B"
| wtPCon:
    "k < length (pcons (S h)) \<Longrightarrow>
      length as = length (pcons (S h) ! k) \<Longrightarrow>
      (\<forall>i < length as.
        wt S D G (as ! i) (argTy h (pcons (S h) ! k ! i))) \<Longrightarrow>
      wt S D G (PCon h k as) (Hit h)"
| wtLCon:
    "j \<in> D \<Longrightarrow> k < length (lcons (S h)) \<Longrightarrow>
      length as = length (lcons (S h) ! k) \<Longrightarrow>
      (\<forall>i < length as.
        wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))) \<Longrightarrow>
      wt S D G (LCon h k as (DVar j)) (Hit h)"
| wtElim:
    "wt S D G t (Hit h) \<Longrightarrow>
      length pms = length (pcons (S h)) \<Longrightarrow>
      length lms = length (lcons (S h)) \<Longrightarrow>
      (\<forall>k < length pms.
        wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))) \<Longrightarrow>
      (\<forall>k < length lms.
        wt S (insert 0 D) G (lms ! k)
          (methodTy h C (lcons (S h) ! k))) \<Longrightarrow>
      wt S D G (HElim h C pms lms t) C"

subsection \<open>Applying a method to the eliminator arguments\<close>

text \<open>
  The computation rules replace an eliminator at a constructor by the
  corresponding method applied to \<^const>\<open>elimArgs\<close>.  The following lemma is
  the typing analogue: a method of the declared type, applied to arguments
  of the declared kinds, lands in the motive.
\<close>

lemma wt_apps_elimArgs:
  assumes E: "\<And>a. wt S D G a (Hit h) \<Longrightarrow>
      wt S D G (HElim h C pms lms a) C"
  shows "\<And>as m. length as = length ss \<Longrightarrow>
    (\<forall>i < length ss. wt S D G (as ! i) (argTy h (ss ! i))) \<Longrightarrow>
    wt S D G m (methodTy h C ss) \<Longrightarrow>
    wt S D G (apps m (elimArgs h C pms lms ss as)) C"
proof (induct ss)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  from Cons(2) obtain a as' where as: "as = a # as'"
    and len: "length as' = length ss"
    by (cases as) auto
  have a0: "wt S D G a (argTy h s)"
    using Cons(3) as by force
  have rest: "\<forall>i < length ss. wt S D G (as' ! i) (argTy h (ss ! i))"
    using Cons(3) as by fastforce
  show ?case
  proof (cases s)
    case (Par h')
    then have "wt S D G a (Hit h')" using a0 by simp
    moreover from Cons(4) Par
      have "wt S D G m (Fun (Hit h') (methodTy h C ss))" by simp
    ultimately have "wt S D G (App m a) (methodTy h C ss)"
      by (rule wt.wtApp[rotated])
    then have "wt S D G (apps (App m a) (elimArgs h C pms lms ss as')) C"
      by (rule Cons(1)[OF len rest])
    then show ?thesis using as Par by simp
  next
    case Rec
    then have aH: "wt S D G a (Hit h)" using a0 by simp
    from Cons(4) Rec
      have "wt S D G m (Fun (Hit h) (Fun C (methodTy h C ss)))" by simp
    from wt.wtApp[OF this aH]
      have step: "wt S D G (App m a) (Fun C (methodTy h C ss))" .
    have "wt S D G (App (App m a) (HElim h C pms lms a)) (methodTy h C ss)"
      by (rule wt.wtApp[OF step E[OF aH]])
    then have "wt S D G
        (apps (App (App m a) (HElim h C pms lms a))
          (elimArgs h C pms lms ss as')) C"
      by (rule Cons(1)[OF len rest])
    then show ?thesis using as Rec by simp
  qed
qed

end
