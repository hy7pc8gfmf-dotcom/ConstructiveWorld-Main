(* ==========================================================================)
   Arch_PA_02.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：fa57_sum_carrier_realizes、fa57_sumd_mult_const_r、fa57_lt_minus_nonneg、fa57_minus_lt_strict、fa57_nat_to_R、fa57_nat_to_R_pos、fa57_grpo_G_pos、fa57_two、fa57_two_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa53_compat_abs.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import List.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpAblMetaWorld3.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
From Stdlib Require Import Lia Setoid Morphisms Qfield.
From Stdlib Require Import Extraction.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.

(* ================= §1 fa57_sum_carrier_realizes 族 ================= *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa57Ext.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
(* fa53 件依存位：单侧严格平移族需可判定序扩展（ 先例：
   @ 全参显式喂 DO； discharge 后 DO 仅进簇二两件签名，与 fa53 件1
   槽实例化消解口径同阶——UpFirewall:104/UpEntropyGain:86 槽的诚实消解形） *)
Context {DO : DecidableOrder RI}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

(*   pos_preserved：逐点正 ⟹ 和正；ext：逐点相等 ⟹ 和相等；            *)
(*   linear：和 (a·f) == a·(和 f)。本包给 sigT 见证：list 折叠。        *)

Theorem fa57_sum_carrier_realizes :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> R) -> R =>
            And (forall f : X -> R,
                   (forall x : X, lt zero (f x)) -> lt zero (sumf f))
                (And (forall f g : X -> R,
                        (forall x : X, Id (f x) (g x)) -> Id (sumf f) (sumf g))
                     (forall (a : R) (f : X -> R),
                        Id (sumf (fun x => mult a (f x)))
                           (mult a (sumf f))))).
Proof.
  intros X enum Hne.
  exact (existT _                (fun f => fa51_sumd X f enum)                ((fun f Hf => fa51_sumd_nonnil_pos X f enum Hne Hf),                 ((fun f g Hpt => fa56b_sumd_cong X f g enum Hpt),                  (fun a f => fa56_sumd_mult_const X a f enum)))).
Qed.

(* ---- 右因子线性（G02:174 之 (fun x => mult (f x) a) 变体）：
        swap（fa56b）× const（fa56）× comm 三步 Id 链。 ---- *)
Lemma fa57_sumd_mult_const_r :
  forall (X : Set) (a : R) (f : X -> R) (l : list X),
    Id (fa51_sumd X (fun x => mult (f x) a) l)
       (mult (fa51_sumd X f l) a).
Proof.
  intros X a f l.
  exact (id_trans (fa56b_sumd_cong X (fun x => mult (f x) a)                                    (fun x => mult a (f x)) l                                    (fun x => mult_comm (f x) a))                  (id_trans (fa56_sumd_mult_const X a f l)                            (mult_comm a (fa51_sumd X f l)))).
Qed.

(* 槽语句：lt a b ⟹ lt zero (minus b a)（minus 定义性 = plus·opp）。     *)
(* 正向：a+(opp a)==zero 归位＋fa53 单侧严格平移。                        *)

Lemma fa57_lt_minus_nonneg :
  forall a b : R, lt a b -> lt zero (minus b a).
Proof.
  intros a b Hab.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a))           (id_sym (plus_opp a))           (@fa53_lt_plus_translate_r RI DO a b (opp a) Hab)).
Qed.

(* 逆向（与 G01:685 le_of_minus_nonneg 严格档对偶）：
   zero 平移回移＋assoc/opp/zero 恒等运河。 *)
Lemma fa57_minus_lt_strict :
  forall a b : R, lt zero (minus b a) -> lt a b.
Proof.
  intros a b H.
  apply (lt_id_l a (plus zero a) b
           (id_trans (id_sym (plus_zero a)) (id_sym (plus_comm zero a)))).
  apply (lt_id_r (plus zero a) (plus (plus b (opp a)) a) b).
  - exact (id_trans (id_sym (plus_assoc b (opp a) a))
                    (id_trans (id_cong (fun w => plus b w)
                                       (id_trans (plus_comm (opp a) a)
                                                 (plus_opp a)))
                              (plus_zero b))).
  - exact (@fa53_lt_plus_translate_r RI DO zero (plus b (opp a)) a H).
Qed.

(* 参数位：G := nat_to_R_g (length group_enum)；G_pos : lt zero G 原为 Variable。
   兑现＝cover（全称 InT 见证）＋任点 g0 ⟹ enum 非空（nil 支由 InT 零
   构造子灭）⟹ length 定义性 S k ⟹ 正性归纳件。载体按既有先例本地
   重声明（UpGRPO.v:51-65 同构：S 位 plus one 递归＋plus_positive/
   one_pos 归纳，证体逐字同构）。 *)

Fixpoint fa57_nat_to_R (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S m => plus one (fa57_nat_to_R m)
  end.

Lemma fa57_nat_to_R_pos :
  forall k : nat, lt zero (fa57_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - exact (lt_id_r zero one (plus one zero) (id_sym (plus_zero one)) one_pos).
  - exact (plus_positive one (fa57_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

Theorem fa57_grpo_G_pos :
  forall (Group : Set) (group_enum : list Group),
    (forall i : Group, InT i group_enum) ->
    forall g0 : Group,
      lt zero (fa57_nat_to_R (Datatypes.length group_enum)).
Proof.
  intros Group group_enum cover g0.
  (* 对 InT 推导本身归纳：两构造子皆 cons 形，Nil 支不进证明项
     （G04 projp_single_le_sum 同法；规避空匹配的提取魔力包装）。 *)
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
Qed.

(* ==================== 簇四：G04 W2' 簇两点均匀投影族 ==================== *)
(* -181/394-400 参数位面（I/f/idx/f_norm/f_pos/P_witness）
   的两点均匀实例全兑现。I:=bool、idx:=[true;false]、f≡half、
   P≡true。half 归一链：half+half==half·1+half·1==half·two==one
   （distrib＋mult_one＋mult_comm＋inv_pos_correct 四段）。          *)

Definition fa57_two : R := plus one one.

Lemma fa57_two_pos : lt zero fa57_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition fa57_half : R := inv_pos fa57_two fa57_two_pos.

Lemma fa57_half_pos : lt zero fa57_half.
Proof.
  exact (inv_pos_pos fa57_two fa57_two_pos).
Qed.

Lemma fa57_half_plus_half : Id (plus fa57_half fa57_half) one.
Proof.
  exact (id_trans (id_cong2 plus (id_sym (mult_one fa57_half))                                (id_sym (mult_one fa57_half)))                  (id_trans (id_sym (distrib fa57_half one one))                            (id_trans (mult_comm fa57_half fa57_two)                                      (inv_pos_correct fa57_two fa57_two_pos)))).
Qed.

(* ---- W2' 七槽面兑现包（norm/pos/witness 三槽 + 结构槽由类型面自证）---- *)
Theorem fa57_W2p_uniform_two_realized :
  And (Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one)
      (And (forall i : bool, lt zero ((fun _ : bool => fa57_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  split.
  - exact (id_trans (id_cong (fun w : R => plus fa57_half w)
                             (plus_zero fa57_half))
                    fa57_half_plus_half).
  - split.
    + exact (fun _ => fa57_half_pos).
    + exact (existT (fun i : bool =>
                       And (Id ((fun _ : bool => true) i) true)
                           (InT i [true; false]))
                    true (id_refl, @InT_here bool true [false])).
Qed.

(* 参数位：Z_align : Real（裸参数位）＋Z_align_pos : lt zero Z_align（诚实参数位）。
   装载＝fa51_Z_align 真实器一次喂定两槽（CYC6 槽装载先例；
   UpDPOLip 节内以该真实器实例化即销两槽）。 *)

Definition fa57_dpolip_Z_realizer :
  forall (X : Set) (enum : list X) (reward : X -> R) (beta : R)
         (beta_pos : lt zero beta) (pi_ref : X -> R),
    (forall s : X, lt zero (pi_ref s)) ->
    Not (Id enum nil) ->
    sigT (fun Z : R => And (Id Z (fa51_Z_align X enum reward beta beta_pos pi_ref))
                           (lt zero Z)).
Proof.
  intros X enum reward beta beta_pos pi_ref Href Hne.
  exact (existT _
                (fa51_Z_align X enum reward beta beta_pos pi_ref)
                (id_refl,
                 fa51_Z_align_pos X enum reward beta beta_pos pi_ref Href Hne)).
Qed.

End Fa57Ext.

(* ============ 假设面闭合申报（G4 前置） ============ *)

Print Assumptions fa57_sum_carrier_realizes.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_minus_lt_strict.
Print Assumptions fa57_grpo_G_pos.
Print Assumptions fa57_W2p_uniform_two_realized.
Print Assumptions fa57_dpolip_Z_realizer.

Print Assumptions fa57_half_plus_half.
Print Assumptions fa57_half_pos.
Print Assumptions fa57_two_pos.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_sum_carrier_realizes.
(* ================= §2 sqrt_half_proj 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Local Open Scope Q_scope.

(* Part 0：Real 层逐点工具（½x + ½x == x，逐点 Q 环恒等）        *)

(* 逐点：projT1 (real_mult (real_const ½) x) n == ½·x_n（组装投影引理） *)
Lemma sqrt_half_proj : forall (x : Real) (n : nat),
  projT1 (real_mult (real_const (1#2)) x) n == (1#2) * projT1 x n.
Proof.
  intros x n.
  rewrite (real_mult_const_proj (1#2) x n).
  rewrite (real_const_proj (1#2) n).
  reflexivity.
Qed.

(* ½·x + ½·x == x（real_eq 逐点；Q 层恒等 ½q + ½q == q 由 ring 判定） *)
Lemma sqrt_real_plus_half_half : forall x : Real,
  real_eq (real_plus (real_mult (real_const (1#2)) x)
                     (real_mult (real_const (1#2)) x))
          x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  (* 差的逐点化简：½x_n + ½x_n − x_n == 0 *)
  assert (Hd : projT1 (real_plus (real_mult (real_const (1#2)) x)
                                 (real_mult (real_const (1#2)) x)) n
                - projT1 x n == 0%Q).
  { rewrite (real_plus_proj (real_mult (real_const (1#2)) x)
                            (real_mult (real_const (1#2)) x) n).
    rewrite (sqrt_half_proj x n).
    ring. }
  (* Qabs(差) == Qabs 0 == 0，逐点界 |0| < eps *)
  assert (Habs0 : Qabs (projT1 (real_plus (real_mult (real_const (1#2)) x)
                                          (real_mult (real_const (1#2)) x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* Part 1（G2）：Real 层构造性平方根存在性                       *)

Theorem real_sqrt_exists : forall d : Real, real_le real_zero d ->
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - 
    exists (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))).
    split.
    + (* r > 0：exp 恒正（real_le 左支 = real_lt） *)
      exact (inl (cauchy_real_exp_pos
              (real_mult (real_const (1#2)) (cw_log d Hdlt)))).
    + 
      apply (real_eq_trans
              (real_mult (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt)))
                         (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                          (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              d).
      * (* 反向用 exp 加法性：exp(x)·exp(y) == exp(x+y) *)
        apply real_eq_sym. apply cauchy_real_exp_plus.
      * apply (real_eq_trans
                (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                            (real_mult (real_const (1#2)) (cw_log d Hdlt))))
                (cauchy_real_exp (cw_log d Hdlt)) d).
        -- 
           apply cauchy_real_exp_wd.
           apply sqrt_real_plus_half_half.
        -- 
           apply cw_log_exp_right.
  - (* 情形②：d ≡ 0（real_eq 证书 Hdeq）。r := real_zero。 *)
    exists real_zero.
    split.
    + (* 0 ≥ 0：real_le 右支 = real_eq 0 0（自反） *)
      exact (inr (real_eq_refl real_zero)).
    + (* 0·0 == 0 == d *)
      apply (real_eq_trans (real_mult real_zero real_zero) real_zero d).
      * apply real_mult_zero.
      * exact Hdeq.
Qed.

(* 具体实例（机器可提取的健全性检查）：1 的平方根可构造。        *)
(*   r := exp(½·log 1)，r ≥ 0 且 r·r == 1——G2 主定理的 d=1 实例。 *)

Lemma real_one_pos_local : real_lt real_zero real_one.
Proof.
  exists (1#2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn. reflexivity.
Qed.

Lemma real_sqrt_one :
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) real_one)).
Proof.
  exact (real_sqrt_exists real_one (inl real_one_pos_local)).
Qed.

(* Part 2（G1）：一般平方维数见证（抽象 R 层，接口泛型）          *)
(*   库内机器检查实例此前仅 d=4（sq_witness_4）；本节给出一般    *)
(*   k² 维数的 sqrt_witness 见证族与对偶实例。                   *)

Section SqrtWitnessGeneral.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* nat → R 嵌入复用库内 nat_to_R（RI 隐式实例参数）。           *)

(* 加法同态：nat_to_R (m+n) == nat_to_R m + nat_to_R n          *)
Lemma nat_to_R_plus_hom : forall m n : nat,
  Id (nat_to_R (m + n)%nat) (plus (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (plus_comm zero (nat_to_R n))
                            (plus_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (id_cong (fun t => plus one t) IH)
                    (plus_assoc one (nat_to_R m) (nat_to_R n))).
Qed.

(* 乘法同态：nat_to_R (m·n) == nat_to_R m · nat_to_R n          *)
Lemma nat_to_R_mult_hom : forall m n : nat,
  Id (nat_to_R (m * n)%nat) (mult (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (mult_comm zero (nat_to_R n))
                            (mult_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (nat_to_R_plus_hom n (m * n)%nat)
           (id_trans (id_cong (fun t => plus (nat_to_R n) t) IH)
           (id_trans (id_cong (fun t => plus t (mult (nat_to_R m) (nat_to_R n)))
                              (id_sym (mult_one (nat_to_R n))))
           (id_trans (id_cong (fun t => plus (mult (nat_to_R n) one) t)
                              (mult_comm (nat_to_R m) (nat_to_R n)))
           (id_trans (id_sym (distrib (nat_to_R n) one (nat_to_R m)))
                     (mult_comm (nat_to_R n) (plus one (nat_to_R m)))))))).
Qed.

(* nat_to_R 的严格正性：k ≥ 1 ⟹ 0 < nat_to_R k                 *)
Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl.
    exact (lt_id_r zero one (plus one zero)
                   (id_sym (plus_zero one)) one_pos).
  - simpl. exact (plus_positive one (nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* 见证（字面形式）：d := r·r（Id 自反；即「r 即 √(r²)」的命名式） *)
Lemma sqrt_witness_sq : forall k : nat,
  sqrt_witness (mult (nat_to_R k) (nat_to_R k)) (nat_to_R k).
Proof. intro k. exact id_refl. Qed.

(* 见证（非平凡形式）：d := nat_to_R (k·k) == nat_to_R k · nat_to_R k
   （由乘法同态 nat_to_R_mult_hom 给出——k² 维数的真见证）      *)
Lemma sqrt_witness_nat_sq : forall k : nat,
  sqrt_witness (nat_to_R (k * k)%nat) (nat_to_R k).
Proof. intro k. exact (id_sym (nat_to_R_mult_hom k k)). Qed.

(* k² 维数对偶实例：1/(S k) 缩放 == 温度 (S k)
   （scale_sqrt_witness_dual 在 d := nat_to_R (S k) · nat_to_R (S k)、
     r := nat_to_R (S k) 的实例化；k ≥ 0 ⟹ 温度 ≥ 1 > 0）       *)
Lemma scale_dual_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (mult (nat_to_R (Datatypes.S k)) (nat_to_R (Datatypes.S k)))           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_sq (Datatypes.S k)) z s).
Qed.

(* 对偶实例（nat 平方形式，d := nat_to_R ((S k)·(S k))）         *)
Lemma scale_dual_nat_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (nat_to_R ((Datatypes.S k) * (Datatypes.S k))%nat)           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_nat_sq (Datatypes.S k)) z s).
Qed.

End SqrtWitnessGeneral.

Print Assumptions scale_dual_nat_sq_k.
Print Assumptions scale_dual_sq_k.
Print Assumptions sqrt_witness_nat_sq.
Print Assumptions sqrt_witness_sq.
Print Assumptions real_sqrt_one.
(* ================= §3 mwi_step 族 ================= *)
Import RealInterfaceEnhancedMod.

(* §1 退化侧机器：泛型核一步演化 + 基座代数桥                                      *)

(* 泛型一步演化器：与供体 mtw_step 同构，核 K 提升为显式参数 *)
Definition mwi_step (K : bool -> bool -> Real) (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (K true s')) (mult (mu false) (K false s')).

(* 左零乘：0·a == 0（基座 mult_zero 仅右零形，comm 桥） *)
Lemma mwi_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans (mult zero a) (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* 自差为零：a − a == 0 *)
Lemma mwi_req_minus_self : forall a : Real, req (req_minus a a) zero.
Proof.
  intro a.
  unfold req_minus.
  exact (plus_opp a).
Defined.

(* 零的绝对值：|0| == 0 *)
Lemma mwi_abs_zero : req (abs zero) zero.
Proof. exact abs_zero. Defined.

(* §2 退化面定理：核行全同 ⟹ 一步退化（TV == 0，混合窗退化侧）                      *)
(*   注：行随机前提为世界资格前提；退化本体只需行全同（两行同为首行）。                *)

Theorem mwi_collapse_row_equal :
  forall K : bool -> bool -> Real,
    (forall s : bool, req (plus (K s true) (K s false)) one) ->
    (forall s s' : bool, req (K s s') (K true s')) ->
    req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero.
Proof.
  intros K Hrow Heq.
  (* 质量对在核 K 下一步演化逐点等于首行：mu0 侧 = 1·K(t,·) + 0·K(f,·) *)
  assert (Ht : forall s' : bool, req (mwi_step K mtw_mu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_mu0 s')
                     (plus (K true s') zero)
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_mu0 true) (K true s')) (K true s')
               (mult (mtw_mu0 false) (K false s')) zero
               (req_mult_one_l (K true s'))
               (mwi_mult_zero_l (K false s'))).
    - exact (plus_zero (K true s')). }
  (* nu0 侧 = 0·K(t,·) + 1·K(f,·) = K(f,·) = K(t,·)（行全同） *)
  assert (Hf : forall s' : bool, req (mwi_step K mtw_nu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_nu0 s')
                     (plus zero (K false s'))
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_nu0 true) (K true s')) zero
               (mult (mtw_nu0 false) (K false s')) (K false s')
               (mwi_mult_zero_l (K true s'))
               (req_mult_one_l (K false s'))).
    - exact (req_trans (plus zero (K false s')) (K false s') (K true s')
               (req_plus_zero_l (K false s'))
               (Heq false s')). }
  (* 逐点差为零 ⟹ 逐点绝对值为零 *)
  assert (Hz : forall s' : bool,
           req (abs (req_minus (mwi_step K mtw_mu0 s')
                               (mwi_step K mtw_nu0 s'))) zero).
  { intro s'.
    apply (req_trans
             (abs (req_minus (mwi_step K mtw_mu0 s')
                             (mwi_step K mtw_nu0 s')))
             (abs zero) zero).
    - exact (req_abs_compat
               (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
               zero
               (req_trans
                  (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
                  (req_minus (K true s') (K true s'))
                  zero
                  (req_plus_compat
                     (mwi_step K mtw_mu0 s') (K true s')
                     (opp (mwi_step K mtw_nu0 s')) (opp (K true s'))
                     (Ht s')
                     (req_opp_compat (mwi_step K mtw_nu0 s') (K true s')
                               (Hf s')))
                  (mwi_req_minus_self (K true s')))).
    - exact mwi_abs_zero. }
  (* TV = (1/2)·(0+0) = 0 *)
  apply (req_trans (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0))
                   (mult mtw_half zero) zero).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mwi_step K mtw_mu0 s)
                                  (mwi_step K mtw_nu0 s))))
             zero
             (req_refl mtw_half)
             (req_trans
                (mtw_sumf (fun s : bool =>
                      abs (req_minus (mwi_step K mtw_mu0 s)
                                     (mwi_step K mtw_nu0 s))))
                (plus zero zero) zero
                (req_plus_compat
                   (abs (req_minus (mwi_step K mtw_mu0 true)
                                   (mwi_step K mtw_nu0 true))) zero
                   (abs (req_minus (mwi_step K mtw_mu0 false)
                                   (mwi_step K mtw_nu0 false))) zero
                   (Hz true) (Hz false))
                (req_plus_zero_l zero))).
  - exact (mult_zero mtw_half).
Defined.

(* §3 退化世界显式实例：均匀核（每行 (1/2,1/2)，行全同）TV(1) == 0                  *)

Definition mwi_Kunif (s s' : bool) : Real := mtw_half.

Lemma mwi_Kunif_row : forall s : bool,
  req (plus (mwi_Kunif s true) (mwi_Kunif s false)) one.
Proof. intro s. exact mtw_hh_one. Defined.

Lemma mwi_Kunif_rows_eq : forall s s' : bool,
  req (mwi_Kunif s s') (mwi_Kunif true s').
Proof. intros s s'. exact (req_refl mtw_half). Defined.

Theorem mwi_degenerate_collapse_uniform :
  req (mtw_tv (mwi_step mwi_Kunif mtw_mu0) (mwi_step mwi_Kunif mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal mwi_Kunif mwi_Kunif_row mwi_Kunif_rows_eq).
Defined.

(* §4 主件：双侧混合窗定理（S01 基座 Set 层合取承载）                               *)
(*   左肢=退化侧（退化世界窗退化）；右肢=存在侧（非退化世界窗真实存在：               *)
(*   精确幂律 + 预算下界两个合取肢合取）。                                              *)

Theorem mtw_window_two_sided :
  And
    (* 退化侧：核行全同的行随机核 ⟹ 一步退化 TV == 0 *)
    (forall K : bool -> bool -> Real,
       (forall s : bool, req (plus (K s true) (K s false)) one) ->
       (forall s s' : bool, req (K s s') (K true s')) ->
       req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero)
    (* 存在侧：非退化世界（World3）精确幂律 + 混合窗预算下界 *)
    (And
       (forall n : nat,
          req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
              (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
       (forall (n : nat) (B : Real),
          lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
          lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
Proof.
  split.
  - exact mwi_collapse_row_equal.
  - split.
    + exact mtw_tv_exact_iter.
    + exact mtw_no_mixing_below.
Defined.

(* 四项自检：全件 Closed（零新假设）                                              *)

Print Assumptions mwi_step.
Print Assumptions mwi_mult_zero_l.
Print Assumptions mwi_req_minus_self.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_collapse_row_equal.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mtw_window_two_sided.

(* PA 追印段（ 核验副本件） *)
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_req_minus_self.
(* ================= §4 sa_A 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

(* §1 A_n 整数面（肢②）+ 归一桥换算                                     *)

(* A_n := 2^{n+1}·q̃_n 的整数面（nat 承载 Z 化） *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* A_n 的 Q 承载 == 2^{n+1}·q̃_n（bi_q_pow_2 + bk_Qmul_nat 换算） *)
Lemma sa_A_q : forall n : nat,
  ((sa_A n) # 1)%Q
  == ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. rewrite bi_q_pow_2. symmetry. apply bk_Qmul_nat.
Qed.

(* 肢②真证：0 < |A_n|（q̃_n ≥ 3^n ≥ 1 ⟹ A_n ≥ 2） *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (bk_Qn_ge_3pow_nat n) as H3.
    pose proof (bi_pow3_pos n) as Hp.
    pose proof (ln2b_pow_ge1 2 n ltac:(lia)) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* sa_norm_bridge：sa_A n # 1 == 2^{2n+1}·Q_n(1/2)（由 bi_norm_factor
   全等换算；真归一因子 2^{n+1}·q̃_n 的闭式落点） *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. exact (bi_norm_factor n). Qed.

(* §2 clo_n 正性肢（肢③）+ 载体整性/上界支撑面                          *)

(* 载体：clo_n := lne_B n = ∫₀¹ tⁿ(1−t)ⁿ dt 的闭式 (n!)²/(2n+1)! *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* 肢③真证：0 < clo_n（由 lne_B_posT） *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. apply lne_B_posT. Qed.

(* sa_clo_int：载体整性面 clo_n·(2n+1)! == (n!)² ∈ Z（存在型见证——
   B_n 整数面的组合原料；分子侧 Z 化即走此面） *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* sa_clo_le_p4：载体上界面 clo_n ≤ 4^{−n}（I_n ≤ 2^{n+1}·clo_n ≤
   2^{1−n} 的 Q 端原料；积分端半边 1/(1−t/2)^{n+1} ≤ 2^{n+1} 待本体到货） *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* §3 θ 档（肢①）+ 半幂换算                                            *)

Definition sa_theta : Q := (1 # 2)%Q.

(* 肢①真证：θ = 1/2 < 1 *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* sa_theta_posT：θ 正性（ln2b_decay 的前置面） *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* 1 的幂 *)
Lemma sa_qpow_one_q : forall n : nat, q_pow (1 # 1)%Q n == (1 # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

(* 半幂逆：q_pow (1/2) n · q_pow 2 n == 1（ln2b_qpow_inv 换算） *)
Lemma sa_half_pow : forall n : nat,
  q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n == (1 # 1)%Q.
Proof.
  intro n. rewrite (ln2b_qpow_inv 1%Z 2%positive n).
  apply sa_qpow_one_q.
Qed.

(* 半幂逆换算：2^{−n} == (1/2)^n *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  Qinv (q_pow (2 # 1)%Q n) == q_pow (1 # 2)%Q n.
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E. pose proof (bi_q_pow_pos2 n) as Hp.
    apply (Qlt_not_eq 0%Q (q_pow (2 # 1)%Q n) Hp). exact (Qeq_sym _ _ E). }
  assert (Hm := sa_half_pow n).
  assert (H1 : (Qinv (q_pow (2 # 1)%Q n) * q_pow (2 # 1)%Q n)%Q
               == (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n)%Q).
  { rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite Hm. reflexivity. }
  apply (lne_mult_canc _ _ (q_pow (2 # 1)%Q n)); [exact H1 | exact Hnz].
Qed.

(* sa_Qinv_le：Q 逆单调 0 < a ≤ b ⟹ 1/b ≤ 1/a（Q 层支撑引理，Z 分段 nia） *)
Lemma sa_Qinv_le : forall a b : Q, Qlt 0%Q a -> Qle a b -> Qle (Qinv b) (Qinv a).
Proof.
  intros [an ad] [bn bd] Ha Hab.
  unfold Qlt, Qle in Ha, Hab. cbn [Qnum Qden] in Ha, Hab.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* sa_theta_leg_scaffold（纯 Q 换算，真证）：1/(2^{n+1}·q̃_n) ≤
   (1/2)^n = θ^n——误差端 2^{−2n}/q̃_n ≤ θ^n 的收尾档（q̃_n ≥ 3^n ≥ 1） *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'.
  setoid_rewrite <- (sa_theta_pow_inv2 n).
  apply sa_Qinv_le.
  - apply bi_q_pow_pos2.
  - assert (Hq1 : (1 <= bk_Qn_qtilde n)%nat).
    { pose proof (bk_Qn_ge_3pow_nat n) as H3.
      pose proof (bi_pow3_pos n) as Hp. lia. }
    setoid_rewrite (bi_q_pow_2 (Datatypes.S n)).
    setoid_rewrite (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n)).
    setoid_rewrite (bi_q_pow_2 n).
    apply bk_Qle_nat. rewrite Nat.pow_succ_r'. nia.
Qed.

(* sa_clo_in_theta_window（真证）：clo_n < θ^n（n ≥ 1）——载体严格落入
   θ 档判定窗（lne_B_lt_p2 的 2^{−n} 窗经 sa_theta_pow_inv2 换算） *)
Theorem sa_clo_in_theta_window : forall n : nat, (1 <= n)%nat ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (QltT_to_Qlt _ _ (lne_B_lt_p2 n Hn)).
  - reflexivity.
  - unfold sa_theta.
    rewrite ln2i_p2_Z. rewrite <- (bi_q_pow_2 n).
    apply sa_theta_pow_inv2.
Qed.

(* §4 三肢独立封装件（①②③已装面）                                      *)

(* sa_supply_head：supply 五肢之①②③的独立封装 *)
Definition sa_supply_head : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun clo : nat -> Q =>
      sigT (fun th : Q =>
        And (QltT th (1 # 1))
          (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
               (forall n : nat, QltT 0 (clo n)))))).

Theorem sa_supply_three_legs : sa_supply_head.
Proof.
  exists sa_A. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + apply sa_clo_posT.
Qed.

(* §5 条件接口（④⑤肢）+ 两段式装配闭合                                  *)

(* sa_supply_rem：条件接口 B_n 整数面 + ④下界/⑤上界两实数肢——恒等式
   本体（I_n = 2^{n+1}·q̃_n·X − r_n，三子件见头注）到货后的实例化消解槽。
   语义精确：本接口非空性即 θ 档 Padé 逼近列的存在性，本件不妄断。 *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* sa_supply_assemble：两段式装配——三肢已装面 + 条件接口 ⟹ supply 全型 *)
Theorem sa_supply_assemble : forall Hm : sa_supply_rem, ln2i_pade_supply.
Proof.
  intros [B [Hlow Hup]].
  exists sa_A. exists B. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + split.
      * apply sa_clo_posT.
      * split.
        -- exact Hlow.
        -- exact Hup.
Qed.

(* sa_ln2_irrational：ln2 无理数两段式闭合——由 Ln2Bridge  源模块
   ln2b_irrational_from_supply（真走 lic_irrational_criterion，零旁路）。
   语句面 = L4 结论面的展开形（全 Set：sigT/And/QltT/real_lt）。 *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q.
  exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* §6 数值锚组（vm_compute 精确判定：A_1 = 2²·q̃_1 = 12，                 *)
(*    A_2 = 2³·q̃_2 = 104，clo_1 = 1/6，θ² 半幂锚）                      *)

Theorem sa_A1_anchor : QeqT ((sa_A 1) # 1)%Q (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_A2_anchor : QeqT ((sa_A 2) # 1)%Q (104 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_clo1_anchor : QeqT (sa_clo 1) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_theta2_anchor : QeqT (q_pow sa_theta 2) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* §7 提取复核与假设审计                                                 *)

Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.

Print Assumptions sa_ln2_irrational.
Print Assumptions sa_clo_le_p4.
Print Assumptions sa_clo_int.
Print Assumptions sa_clo_posT.
Print Assumptions sa_norm_bridge.
(* ================= §5 frd_req_entropy_temp_explici 族 ================= *)
Import RealInterfaceEnhancedMod.

(* Section FrdTempDischarge：宿主 Section FirewallReq 见证面与          *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。见证每型     *)
(*   一个，宿主位/消解位同喂（重述桥判定见头注）。                      *)
Section FrdTempDischarge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis frd_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis frd_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis frd_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis frd_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis frd_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis frd_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

Hypothesis frd_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis frd_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis frd_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis frd_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis frd_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Theorem frd_req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
  req (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss Z_temp
                           frd_Z_temp_spec t Ht)
      (plus (mult (inv_pos t Ht)
                  (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos base_loss
                                        Z_temp frd_Z_temp_spec t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (UpReqTempEntropy.req_entropy_temp_explicit           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t Ht).
Qed.

(*   归一化证人 = fw_norm（fw_ 见证同喂）。                              *)
Theorem frd_req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss Z_temp
                            frd_Z_temp_spec t1 t2 Ht1 Ht2)
      (plus (plus (opp (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos
                                            base_loss Z_temp
                                            frd_Z_temp_spec t1 Ht1))
                  (mult (inv_pos t2 Ht2)
                        (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                              base_loss Z_temp
                                              frd_Z_temp_spec t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  exact (UpReqTempEntropy.req_relative_entropy_temp_decomp           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t2 Ht2           (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss Z_temp                                 frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss                                    Z_temp frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_norm R RIS S sumf frd_sum_linear frd_sum_pos                                   base_loss Z_temp frd_Z_temp_spec t1 Ht1)).
Qed.

(*   A_chain2 交叉，装配链完备）。                                       *)
Theorem frd_req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                       (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpReqTempEntropy.req_temp_strict_ident2           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(*   槽A/槽B 参位实喂上面两重申件。                                     *)
Theorem frd_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (plus (mult (inv_pos t2 Ht2)
                  (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                    base_loss Z_temp
                                                    frd_Z_temp_spec t2 Ht2)
                             (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                   base_loss Z_temp
                                                   frd_Z_temp_spec t1 Ht1)))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           t1 t2 Ht1 Ht2).
Qed.

(*   重申件 C（槽A/槽B 经件4 链式带入）。三槽替换至此全闭环。           *)
Theorem frd_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1)
                       (req_minus (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t2 Ht2)
                                  (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t1 Ht1)))
                 (req_relative_entropy S sumf
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t1 Ht1)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain_alt           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           frd_req_temp_strict_ident2           t1 t2 Ht1 Ht2).
Qed.

End FrdTempDischarge.

(* Print Assumptions 假设审计（五件全量；与 bbd/enp 文末同款惯例），     *)
(* 语句面零改动、零新增假设位。                                          *)
Print Assumptions frd_req_entropy_temp_explicit.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_recovery_entropy_gain_alt.

(* PA 追印段（ 核验副本件） *)
Print Assumptions frd_recovery_entropy_gain_alt.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_entropy_temp_explicit.
(* ================= §6 pint_eval 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.

(* §A 定义（全 Set 面；载体 Q；多项式 = 系数列表，头为常数项）         *)

(* 求值（Horner 复现）：pint_eval p x = a_0 + x·(a_1 + x·(…)) = Σ a_k x^k *)
Fixpoint pint_eval (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: p' => a + x * pint_eval p' x
  end.

(* 单项式积分值：∫_0^1 a·x^k dx = a/(k+1)（k+1 于 Q 内非零，除法全定义） *)
Definition pint_monomial_int (a : Q) (k : nat) : Q :=
  a / (Z.of_nat (Datatypes.S k) # 1).

(* 定积分（起始偏移 k 版，供归纳；第 i 项系数配分母 k+i+1） *)
Fixpoint pint_integral_from (p : list Q) (k : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' => pint_monomial_int a k + pint_integral_from p' (Datatypes.S k)
  end.

(* [0,1] 定积分主定义 *)
Definition pint_integral (p : list Q) : Q := pint_integral_from p 0.

(* x^k 的系数列表编码：k 个 0 接一个 1 *)
Fixpoint pint_pow_poly (k : nat) : list Q :=
  match k with
  | 0%nat => 1 :: []
  | Datatypes.S m => 0 :: pint_pow_poly m
  end.

(* 逐项运算：数乘 / 加法（等长语义）/ 取第 i 项系数（越界为 0） *)
Fixpoint pint_scale (a : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | c :: p' => a * c :: pint_scale a p'
  end.

Fixpoint pint_add (p q : list Q) : list Q :=
  match p with
  | [] => q
  | a :: p' =>
      match q with
      | [] => p
      | b :: q' => a + b :: pint_add p' q'
      end
  end.

Fixpoint pint_coeff (p : list Q) (i : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' =>
      match i with
      | 0%nat => a
      | Datatypes.S i' => pint_coeff p' i'
      end
  end.

(* §B Q 层内部支撑（== / Qle 仅证内面）                               *)

(* 0 除任意 Q 为 0（Qdiv = 乘 Qinv，零乘一步） *)
Lemma pint_zero_div : forall d : Q, 0 / d == 0.
Proof. intros d. unfold Qdiv. apply Qmult_0_l. Qed.

(* 乘法对除法的结合：(a·c)/d == a·(c/d) *)
Lemma pint_div_mult_assoc : forall a c d : Q, a * c / d == a * (c / d).
Proof. intros a c d. unfold Qdiv. ring. Qed.

(* 除法对加法的分配：(a+b)/d == a/d + b/d *)
Lemma pint_div_add_distr : forall a b d : Q, (a + b) / d == a / d + b / d.
Proof. intros a b d. unfold Qdiv. ring. Qed.

(* 1/(k+1) 严格正：Qinv 于 (n#1)（n>0）定义性折回 (1#n)；
   Z.of_nat (Datatypes.S k) 的符号判定经 Nat2Z 桥（Z0 支矛盾、Zneg 支非负矛盾） *)
Lemma pint_invS_pos : forall k : nat, Qlt 0 ((/ (Z.of_nat (Datatypes.S k) # 1))%Q).
Proof.
  intros k.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  assert (Hz : Z.of_nat (Datatypes.S k) <> 0%Z).
  { intros Hc. discriminate Hc. }
  destruct (Z.of_nat (Datatypes.S k)) as [| z | z] eqn:E.
  - exfalso. apply Hz. reflexivity.
  - unfold Qinv, Qlt. cbn [Qnum Qden Qmult]. lia.
  - exfalso. simpl in Hnn. lia.
Qed.

(* 单项式积分非负：0 ≤ a ⟹ 0 ≤ a/(k+1)（QleT' 进出，Qle 仅证内） *)
Lemma pint_monomial_int_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans 0 (0 * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                    (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))).
  - apply qeq_le. apply Qeq_sym. apply Qmult_0_l.
  - apply (Qmult_le_compat_r 0 a).
    + exact (QleT'_to_Qle 0 a Ha).
    + apply Qlt_le_weak. apply pint_invS_pos.
Qed.

(* §C 求值正确性伴侣：pint_pow_poly k 的求值 ≡ q_pow x k（S03 幂引擎） *)

Theorem pint_eval_pow_poly : forall (k : nat) (x : Q),
  QeqT (pint_eval (pint_pow_poly k) x) (q_pow x k).
Proof.
  intros k. induction k as [| m IH]; intros x.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT. ring.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    apply Qplus_0_l.
Qed.

(* §D 正确性锚：∫ x^k == 1/(k+1)（含偏移推广版）                      *)

(* 偏移推广：∫（起始偏移 k）x^m == 1/(k+m+1)。对 m 归纳；                *)
(*   nat 层 S 归一经 lia 桥（Hnat），Z.of_nat 原子两侧同步重写。          *)
Lemma pint_integral_from_pow_poly : forall (m k : nat),
  pint_integral_from (pint_pow_poly m) k == 1 / (Z.of_nat (Datatypes.S (k + m)) # 1).
Proof.
  intros m. induction m as [| m' IH]; intros k.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    rewrite Nat.add_0_r. apply Qplus_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    unfold pint_monomial_int. rewrite pint_zero_div.
    rewrite (IH (Datatypes.S k)).
    assert (Hnat : Datatypes.S (k + Datatypes.S m')
                   = Datatypes.S (Datatypes.S k + m')) by lia.
    rewrite Hnat.
    apply Qplus_0_l.
Qed.

(* 正确性锚（Set 面）：∫_0^1 x^k dx == 1/(k+1) *)
Theorem pint_integral_pow_poly : forall k : nat,
  QeqT (pint_integral (pint_pow_poly k)) (1 / (Z.of_nat (Datatypes.S k) # 1)).
Proof.
  intros k. apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (pint_integral_from_pow_poly k 0).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* 退化锚：∫ 1 == 1 *)
Theorem pint_integral_one : QeqT (pint_integral (pint_pow_poly 0)) (1 # 1).
Proof.
  apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (pint_integral_from_pow_poly 0 0).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* §E 线性性（系数层面偏移版 + 0 偏移组装，Set 面）                    *)

(* 数乘：∫（偏移 k）(a·p) == a·∫（偏移 k）p *)
Lemma pint_integral_from_scale : forall (a : Q) (p : list Q) (k : nat),
  pint_integral_from (pint_scale a p) k == a * pint_integral_from p k.
Proof.
  intros a p. induction p as [| c p' IH]; intros k.
  - cbn [pint_integral_from pint_scale]. symmetry. apply Qmult_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_scale].
    rewrite (pint_div_mult_assoc a c (Z.of_nat (Datatypes.S k) # 1)).
    rewrite (IH (Datatypes.S k)).
    unfold pint_monomial_int. ring.
Qed.

(* 加法（等长前提）：∫（偏移 k）(p+q) == ∫p + ∫q *)
Lemma pint_integral_from_add : forall (p q : list Q) (k : nat),
  length p = length q ->
  pint_integral_from (pint_add p q) k
  == pint_integral_from p k + pint_integral_from q k.
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_add]. ring.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from pint_monomial_int pint_add].
      injection Hlen as Hlen'.
      rewrite (IH q' (Datatypes.S k) Hlen').
      rewrite (pint_div_add_distr a b (Z.of_nat (Datatypes.S k) # 1)).
      unfold pint_monomial_int. ring.
Qed.

(* 组装（0 偏移，QeqT 面） *)
Theorem pint_integral_scale : forall (a : Q) (p : list Q),
  QeqT (pint_integral (pint_scale a p)) (a * pint_integral p).
Proof.
  intros a p.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  apply pint_integral_from_scale.
Qed.

Theorem pint_integral_add : forall p q : list Q,
  length p = length q ->
  QeqT (pint_integral (pint_add p q)) (pint_integral p + pint_integral q).
Proof.
  intros p q Hlen.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  apply pint_integral_from_add.
  exact Hlen.
Qed.

(* §F 单调性加分件（逐项版；QleT' 面，Qle 仅证内）                     *)

(* 逐项非负 ⟹ 偏移积分非负（Qplus_le_compat 双肢：单项式非负肢 +        *)
(*   归纳肢；系数索引偏移由 pint_coeff 的 S 分支定义性对齐）             *)
Lemma pint_integral_from_nonneg : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral_from p k).
Proof.
  intros p. induction p as [| a p' IH]; intros k Hcoeff.
  - reflexivity.
  - cbn [pint_integral_from].
    apply Qle_to_QleT'.
    apply (Qplus_le_compat 0 (pint_monomial_int a k)
                           0 (pint_integral_from p' (Datatypes.S k))).
    + apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QleT'_to_Qle. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 逐项 ≤（等长）⟹ 偏移积分 ≤：双肢 Qmult_le_compat_r（右因子 = 1/(k+1) *)
(*   严格正肢经 pint_invS_pos）+ 归纳肢                                  *)
Lemma pint_integral_from_mono : forall (p q : list Q) (k : nat),
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen Hcoeff.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from].
      injection Hlen as Hlen'.
      apply Qle_to_QleT'.
      apply Qplus_le_compat.
      * unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply pint_invS_pos.
      * apply QleT'_to_Qle. apply IH.
        -- exact Hlen'.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* 组装（0 偏移，QleT' 面） *)
Theorem pint_integral_nonneg : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral p).
Proof.
  intros p H.
  unfold pint_integral.
  apply pint_integral_from_nonneg.
  exact H.
Qed.

Theorem pint_integral_mono : forall p q : list Q,
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hlen Hcoeff.
  unfold pint_integral.
  apply pint_integral_from_mono; assumption.
Qed.

(* 假设审计留痕：Print Assumptions（编译期 stdout，verify 复核）        *)

Print Assumptions pint_integral_pow_poly.
Print Assumptions pint_integral_one.
Print Assumptions pint_eval_pow_poly.
Print Assumptions pint_integral_scale.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_mono.

Print Assumptions pint_integral_mono.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_scale.
Print Assumptions pint_zero_div.
