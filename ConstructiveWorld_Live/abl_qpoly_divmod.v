(* ===================================================================== *)
(*  模块名：abl_qpoly_divmod —— Q 层多项式带余除法引擎首件——ln2 路线③      *)
(*    （S6 恒等式支）唯一无在册先例的代数件的最小可行基座。                  *)
(* 使命：按诚实边界清单，闭合 ln2 路线③「多项式除法引擎」的首件档位——       *)
(*    Q 系数稠密列表多项式（头=常数项，循库内 PolyIntegral 先例）的          *)
(*    【线性除数带余除法（综合除法）】引擎：                                *)
(*      qpd_synth a p : list Q * Q —— p ÷ (x+a) 的（商列表, 余数标量），     *)
(*      真结构 Fixpoint（头递归，非平凡算法体，可提取）；                    *)
(*      qpd_pdivmod_lin_wit a p : sigT 封装（商+余数+双正确性肢）：          *)
(*        ①等式肢 ∀x, QeqT (eval p x) (eval (x+a) x · eval 商 x + 余数)      *)
(*        ②度肢   qpd_deglt 余式列表 (x+a)（Id bool 面，可判定）             *)
(*    一般除法形【只登记不施工】：qpd_divmod_gen_type 留接口；               *)
(*    线性→一般桥 qpd_lin_to_gen 已通（线性引擎经一般接口即接入）。          *)
(* 诚实边界：①一般形引擎不施工——头=常数项表示下一般长除法须自尾（最高次）   *)
(*    剥项，非结构递归；线性综合除法恰是头结构递归的最大可闭合切片，此为      *)
(*    表示法层面的真限制，非证明技巧欠缺。②商列表允许尾随零（稠密表示，      *)
(*    求值语义不受影响，烟测如实呈现）。③qpd_lead 的非平凡引理（如幂单项     *)
(*    首一性）只登记不施工。④使用前瞻（只登记不施工）：AE 路线③ Beukers     *)
(*    恒等式 tⁿ(1−t)ⁿ == P_n·(1−t/2)^{n+1} + Σd_j(1−t/2)^{n+1−j} 的除法      *)
(*    位，本件一般接口 qpd_divmod_gen_type 即其使用面。                     *)
(* 依赖清单：Stdlib QArith/Qring/Qfield/List/Arith/ZArith/Extraction；      *)
(*    S01_BaseRing S02_CauchyComplete PolyIntegral（池外世界树在册件）。     *)
(* 对标：PolyIntegral pint_*（Q 系数列表先例）；BT 诚实边界路线③除法引擎；  *)
(*    AE §3.3 路线③。                                                     *)
(* 构造性注记：纯构造性、零承认件；语句面全 Set（sigT/And/S02.QeqT/S01.Id   *)
(*    度谓词），Qeq==仅证内推理脚手架；环闭全走「全变量形纯环小件」模式。    *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&         *)
(*    ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q             *)
(*    <world> "" 本件（单进程串行）。                                       *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Extraction.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete PolyIntegral.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 表示与度支持件（全 Set 面）                                 *)
(*    多项式 = list Q 稠密系数表，头=常数项（PolyIntegral 先例）； *)
(*    度约定：deg [] = 0（零多项式按度 0 记，度肢由可判定 Id 面    *)
(*    诚实承载，不虚报 −∞ 惯例）。                                *)
(* ============================================================ *)

(* 度：length − 1（空表记 0） *)
Definition qpd_deg (p : list Q) : nat :=
  match p with
  | [] => 0%nat
  | _ :: _ => pred (length p)
  end.

(* 首系数（最高次项系数；越界/空表为 0，复用库内 pint_coeff） *)
Definition qpd_lead (p : list Q) : Q :=
  pint_coeff p (pred (length p)).

(* 度肢可判定谓词：deg r < deg q 的 Id bool 面（Set 层）
   （坑卡：S01.Id 的 A 为最大隐式，@Id 显式给 A，bool 不可省写） *)
Definition qpd_deglt (r q : list Q) : Set :=
  @Id bool true (Nat.ltb (qpd_deg r) (qpd_deg q)).

Lemma qpd_deglt_const : forall (c a : Q), qpd_deglt (c :: nil) (a :: 1 :: nil).
Proof.
  intros c a. unfold qpd_deglt, qpd_deg.
  cbn [length pred Nat.ltb].
  exact id_refl.
Qed.

Lemma qpd_lead_nil : qpd_lead (@nil Q) == 0.
Proof. cbn [qpd_lead pint_coeff]. apply Qeq_refl. Qed.

Lemma qpd_lead_single : forall c : Q, qpd_lead (c :: nil) == c.
Proof. intros c. cbn [qpd_lead pint_coeff length pred]. apply Qeq_refl. Qed.

(* ============================================================ *)
(* §1 全变量形纯环小件组（坑卡 AL/AX 模式：环闭原子全为变量，      *)
(*    调用位以复合项直取代参；杜绝「环闭原子含复合项 ring 失灵」） *)
(* ============================================================ *)

Lemma qpd_ring_0l : forall e : Q, e == 0 + e.
Proof. intros e. ring. Qed.

Lemma qpd_ring_0r : forall e : Q, e == e + 0.
Proof. intros e. ring. Qed.

Lemma qpd_ring_scale0 : forall a : Q, 0 == a * 0.
Proof. intros a. ring. Qed.

Lemma qpd_ring_const : forall r x : Q, r + x * 0 == r.
Proof. intros r x. ring. Qed.

Lemma qpd_ring_lin_eval : forall a x : Q, a + x * (1 + x * 0) == a + x.
Proof. intros a x. ring. Qed.

Lemma qpd_ring_base : forall a x : Q, 0 == (a + x) * 0 + 0.
Proof. intros a x. ring. Qed.

(* 综合除法步核心恒等式：p = c + x·p′，p′ = (x+a)·s′ + r′
   ⟹ c·x⁰ 位的消去：c + x·((a+x)e + r) == (a+x)(r + x·e) + (c − a·r) *)
Lemma qpd_ring_lin_step : forall a c e r x : Q,
  c + x * ((a + x) * e + r) == (a + x) * (r + x * e) + (c - a * r).
Proof. intros a c e r x. ring. Qed.

Lemma qpd_ring_add : forall a b e1 e2 x : Q,
  (a + b) + x * (e1 + e2) == (a + x * e1) + (b + x * e2).
Proof. intros a b e1 e2 x. ring. Qed.

Lemma qpd_ring_scale : forall a c e x : Q,
  a * c + x * (a * e) == a * (c + x * e).
Proof. intros a c e x. ring. Qed.

Lemma qpd_ring_mullin : forall a e x : Q,
  (0 + x * e) + a * e == (x + a) * e.
Proof. intros a e x. ring. Qed.

(* 语义烟测配套：(x²+1) ÷ (x+1) 之商 x−1 的求值恒等式 *)
Lemma qpd_ring_xminus1 : forall x : Q,
  (-1) + x * (1 + x * (0 + x * 0)) == x + (-1).
Proof. intros x. ring. Qed.

(* ============================================================ *)
(* §2 求值脚手架（Horner 求值与系数运算的语义引理；== 仅证内）    *)
(* ============================================================ *)

Lemma qpd_eval_nil : forall x : Q, pint_eval [] x == 0.
Proof. intros x. cbn [pint_eval]. apply Qeq_refl. Qed.

Lemma qpd_eval_cons : forall (c : Q) (p : list Q) (x : Q),
  pint_eval (c :: p) x == c + x * pint_eval p x.
Proof. intros c p x. cbn [pint_eval]. apply Qeq_refl. Qed.

(* 线性除式求值：eval (x+a) x == a + x *)
Lemma qpd_eval_lin_eq : forall a x : Q, pint_eval (a :: 1 :: nil) x == a + x.
Proof.
  intros a x.
  rewrite qpd_eval_cons, qpd_eval_cons, qpd_eval_nil.
  apply (qpd_ring_lin_eval a x).
Qed.

(* 常多项式求值：eval [r] x == r *)
Lemma qpd_eval_const : forall r x : Q, pint_eval (r :: nil) x == r.
Proof.
  intros r x.
  rewrite qpd_eval_cons, qpd_eval_nil.
  apply (qpd_ring_const r x).
Qed.

(* 库内 pint_add（系数加法）的求值语义 *)
Lemma qpd_eval_add : forall (p q : list Q) (x : Q),
  pint_eval (pint_add p q) x == pint_eval p x + pint_eval q x.
Proof.
  intros p q x. revert q.
  induction p as [|a p' IH]; intros q.
  - cbn [pint_add]. rewrite qpd_eval_nil.
    exact (qpd_ring_0l (pint_eval q x)).
  - destruct q as [|b q'].
    + cbn [pint_add]. exact (qpd_ring_0r (pint_eval (a :: p') x)).
    + cbn [pint_add]. rewrite qpd_eval_cons. rewrite (IH q').
      exact (qpd_ring_add a b (pint_eval p' x) (pint_eval q' x) x).
Qed.

(* 库内 pint_scale（数乘）的求值语义 *)
Lemma qpd_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  pint_eval (pint_scale a p) x == a * pint_eval p x.
Proof.
  intros a p x. revert a.
  induction p as [|c p' IH]; intros a.
  - cbn [pint_scale]. rewrite qpd_eval_nil. apply (qpd_ring_scale0 a).
  - cbn [pint_scale]. rewrite qpd_eval_cons. rewrite (IH a).
    exact (qpd_ring_scale a c (pint_eval p' x) x).
Qed.

(* 乘线性式：(x+a)·s 的系数表 = 升位 s + a·s（系数运算组装件） *)
Definition qpd_mul_lin (a : Q) (s : list Q) : list Q :=
  pint_add (0 :: s) (pint_scale a s).

Lemma qpd_eval_mul_lin : forall (a : Q) (s : list Q) (x : Q),
  pint_eval (qpd_mul_lin a s) x == (x + a) * pint_eval s x.
Proof.
  intros a s x. unfold qpd_mul_lin.
  rewrite qpd_eval_add, qpd_eval_scale, qpd_eval_cons.
  exact (qpd_ring_mullin a (pint_eval s x) x).
Qed.

(* ============================================================ *)
(* §3 线性除数综合除法引擎（真 Fixpoint，头=常数项结构递归）       *)
(*    不变式：qpd_synth a p = (s, r) 满足 p == (x+a)·s + r        *)
(*    递归步：c::p′ 中 p′ 已归约出 (s′, r′)，则升位配平得          *)
(*      商 = r′::s′，余 = c − a·r′（一次代入消去 c 位）。          *)
(* ============================================================ *)

Fixpoint qpd_synth (a : Q) (p : list Q) : list Q * Q :=
  match p with
  | [] => ([], 0)
  | c :: p' => let (s', r') := qpd_synth a p' in (r' :: s', c - a * r')
  end.

(* 双正确性肢谓词（Set 面：And × S02.QeqT × Id 度肢） *)
Definition qpd_lin_pred (a : Q) (p : list Q) (s : list Q) (r : Q) : Set :=
  And
    (forall x : Q,
       QeqT (pint_eval p x)
            (pint_eval (a :: 1 :: nil) x * pint_eval s x + r))
    (qpd_deglt (r :: nil) (a :: 1 :: nil)).

Lemma qpd_synth_sound : forall (a : Q) (p : list Q),
  qpd_lin_pred a p (fst (qpd_synth a p)) (snd (qpd_synth a p)).
Proof.
  intros a p. induction p as [|c p' IH].
  - (* 空表基例：0 == (x+a)·0 + 0，余 0 度 0 < 1 *)
    unfold qpd_lin_pred. cbn [qpd_synth fst snd]. split.
    + intros x. apply qeq_imp_qeqT.
      rewrite qpd_eval_nil, qpd_eval_lin_eq.
      apply (qpd_ring_base a x).
    + apply (qpd_deglt_const 0 a).
  - (* 递归步：先解构内层商余，再一步代入消去 c 位 *)
    cbn [qpd_synth]. destruct (qpd_synth a p') as [s' r'] eqn:E.
    unfold qpd_lin_pred in IH. destruct IH as [IH1 IH2].
    unfold qpd_lin_pred. cbn [fst snd]. split.
    + intros x. apply qeq_imp_qeqT.
      assert (Hq : pint_eval p' x
                     == pint_eval (a :: 1 :: nil) x * pint_eval s' x + r')
        by exact (qeqT_imp_qeq _ _ (IH1 x)).
      rewrite qpd_eval_cons.
      rewrite (qpd_eval_cons r' s' x).
      rewrite Hq.
      rewrite (qpd_eval_lin_eq a x).
      exact (qpd_ring_lin_step a c (pint_eval s' x) r' x).
    + exact (qpd_deglt_const (c - a * r') a).
Qed.

(* sigT 封装：{（商, 余）| p == (x+a)·商 + 余 ∧ deg 余 < deg (x+a)} *)
Definition qpd_pdivmod_lin_type (a : Q) (p : list Q) : Set :=
  sigT (fun w : list Q * Q => qpd_lin_pred a p (fst w) (snd w)).

Definition qpd_pdivmod_lin_wit (a : Q) (p : list Q) : qpd_pdivmod_lin_type a p :=
  existT _ (qpd_synth a p) (qpd_synth_sound a p).

(* ============================================================ *)
(* §4 一般除法形接口（只登记不施工）＋ 线性→一般桥（已通）         *)
(*    一般形规格：{（商, 余）| ∀x, eval p == eval q·eval 商 + eval 余 *)
(*                ∧ deg 余 < deg q}——deg 肢自动排除 deg q = 0 的    *)
(*    零除位，规格诚实无需另设非零前提。                           *)
(* ============================================================ *)

Definition qpd_divmod_gen_pred (p q : list Q) (w : list Q * list Q) : Set :=
  And
    (forall x : Q,
       QeqT (pint_eval p x)
            (pint_eval q x * pint_eval (fst w) x + pint_eval (snd w) x))
    (qpd_deglt (snd w) q).

Definition qpd_divmod_gen_type (p q : list Q) : Set :=
  sigT (qpd_divmod_gen_pred p q).

(* 桥：线性引擎产出经一般接口即接入（余数标量升为常多项式 [r]） *)
Lemma qpd_lin_to_gen_sound : forall (a : Q) (p : list Q),
  qpd_divmod_gen_pred p (a :: 1 :: nil)
    (fst (qpd_synth a p), snd (qpd_synth a p) :: nil).
Proof.
  intros a p. unfold qpd_divmod_gen_pred. split.
  - intros x. apply qeq_imp_qeqT.
    rewrite (qpd_eval_const (snd (qpd_synth a p)) x).
    exact (qeqT_imp_qeq _ _ (fst (qpd_synth_sound a p) x)).
  - exact (qpd_deglt_const (snd (qpd_synth a p)) a).
Qed.

Definition qpd_lin_to_gen (a : Q) (p : list Q) : qpd_divmod_gen_type p (a :: 1 :: nil) :=
  existT _ (fst (qpd_synth a p), snd (qpd_synth a p) :: nil)
           (qpd_lin_to_gen_sound a p).

(* ============================================================ *)
(* §5 数值烟测（BF 模式：vm_compute 零公设定装，实例小形）         *)
(*    基准例：(x²+1) ÷ (x+1) ⟹ 商 x−1 余 2                       *)
(* ============================================================ *)

(* 烟测 0：空表边例——0 ÷ (x+3) = 商 0 余 0 *)
Lemma qpd_smoke0 :
  fst (qpd_synth 3 (@nil Q)) = (@nil Q) /\ snd (qpd_synth 3 (@nil Q)) == 0.
Proof.
  split.
  - cbn [qpd_synth fst]. reflexivity.
  - cbn [qpd_synth snd]. apply Qeq_refl.
Qed.

(* 烟测 1（基准例）：(x²+1) ÷ (x+1) ⟹ 商 [−1;1;0]（=x−1，稠密含尾零）余 2 *)
Lemma qpd_smoke1_q :
  fst (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 0 :: 1 :: nil)))
  = (-1) :: 1 :: 0 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpd_smoke1_r :
  snd (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 0 :: 1 :: nil))) == 2.
Proof. vm_compute. reflexivity. Qed.

(* 烟测 1 语义面：商 [−1;1;0] 的求值 == x−1（证内纯环小件直取） *)
Lemma qpd_smoke1_quot_sem : forall x : Q,
  QeqT (pint_eval (fst (qpd_synth 1 (1 :: 0 :: 1 :: nil))) x) (x + (-1)).
Proof.
  intros x. apply qeq_imp_qeqT.
  cbn [qpd_synth fst].
  rewrite qpd_eval_cons, qpd_eval_cons, qpd_eval_cons, qpd_eval_nil.
  apply (qpd_ring_xminus1 x).
Qed.

(* 烟测 2：自除 (x+1) ÷ (x+1) ⟹ 商 1 余 0 *)
Lemma qpd_smoke2_q :
  fst (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 1 :: nil))) = 1 :: 0 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpd_smoke2_r :
  snd (projT1 (qpd_pdivmod_lin_wit 1 (1 :: 1 :: nil))) == 0.
Proof. vm_compute. reflexivity. Qed.

(* 烟测 3：负常数除数 (x²−1) ÷ (x−1) ⟹ 商 x+1 余 0 *)
Lemma qpd_smoke3_q :
  fst (projT1 (qpd_pdivmod_lin_wit (-1) ((-1) :: 0 :: 1 :: nil)))
  = 1 :: 1 :: 0 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpd_smoke3_r :
  snd (projT1 (qpd_pdivmod_lin_wit (-1) ((-1) :: 0 :: 1 :: nil))) == 0.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §6 收束：提取面 + Print Assumptions 逐条取证                   *)
(* ============================================================ *)

Separate Extraction qpd_synth qpd_mul_lin.

Print Assumptions qpd_deglt_const.
Print Assumptions qpd_lead_nil.
Print Assumptions qpd_lead_single.
Print Assumptions qpd_eval_add.
Print Assumptions qpd_eval_scale.
Print Assumptions qpd_eval_mul_lin.
Print Assumptions qpd_eval_lin_eq.
Print Assumptions qpd_eval_const.
Print Assumptions qpd_synth_sound.
Print Assumptions qpd_pdivmod_lin_wit.
Print Assumptions qpd_lin_to_gen.
Print Assumptions qpd_smoke0.
Print Assumptions qpd_smoke1_q.
Print Assumptions qpd_smoke1_r.
Print Assumptions qpd_smoke1_quot_sem.
Print Assumptions qpd_smoke2_q.
Print Assumptions qpd_smoke2_r.
Print Assumptions qpd_smoke3_q.
Print Assumptions qpd_smoke3_r.

(* 多项式除法引擎首件终（纯构造性出生） *)
