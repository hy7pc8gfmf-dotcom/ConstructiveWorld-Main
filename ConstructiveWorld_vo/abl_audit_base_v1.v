(* ==========================================================================)
   abl_audit_base_v1.v — 基座裸奔位独立审计卷第一件（甲形态·零级联）
   使命：形式化四命题 aba_qlt_eps_sub／aba_cauchy_limit_raw／aba_const_seq_
      convergent／aba_gibbs_softmax_explicit——以两条轻量使用面实例定理真行使
      裸奔主定理 S02 real_cauchy_complete（裸奔 Top #1，入度 493 零直审）与
      S06 attention_is_gibbs（裸奔 Top #2，论文 2 主张核心），尾舱对两裸奔
      主定理做跨件 qualified 直审（Print Assumptions 追审型，Z 规格书 2.1/2.4
      口径）。
   依赖清单：S01_BaseRing／S02_CauchyComplete／S03_QExp／S04_RealExpLogConv／
      S05_AlignmentGRPO／S06_DiffSamplingGibbs（Require 全链透传）＋Stdlib
      （QArith、List、Bool、Arith、Setoid、Morphisms）。
   对标行：Z 规格书 2.1/2.4 直审口径；S02 直审卷族体例（v2/v3 同族）。
   构造性注记：全件 Qed 闭合、零承认词面、无经典逻辑；语句面全 Set 层
      （sigT／And／QltT／real_lt／Id 均 Set 型），零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q <缓存根> ""，
      nice 限载（AL/AS 池内配方）；验证＝EXIT=0＋Print Assumptions 全 Closed。
   查重登记：顶层名 4 枚全 aba_ 新前缀，与 v2 abb_／v3 abc_ 及库内既有顶层名
      零撞零别名转发；六条 Print Assumptions 只读直审，上游宿主零字节不动。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.

(* ============================================================ *)
(* §1 裸奔位一（S02 real_cauchy_complete）使用面包装            *)
(*   实例定理把完备性主定理的结论从 real_lim 包装层降到          *)
(*   原始 eps/N 双向夹逼形（dist 收敛包装），并给出常值列        *)
(*   这一具体应用实例——两条均直引主定理本体现闭合。            *)
(* ============================================================ *)

(* Q 层辅助：0 < eps ⟹ eps/2 < eps − (q + (−q))                 *)
(* （常值列柯西假设双向目标的逐点核；q + (−q) 经 Qcompare_comp  *)
(*   换形到 eps，再用 S02 q_half_lt 闭合——照 S02:1436 判例形） *)
Lemma aba_qlt_eps_sub :
  forall (q eps : Q), S02_CauchyComplete.QltT 0%Q eps ->
    S02_CauchyComplete.QltT (eps / 2)%Q (eps - (q + - q)%Q).
Proof.
  intros q eps Heps.
  assert (H0lt : Qlt 0%Q eps)
    by (apply S02_CauchyComplete.QltT_to_Qlt; exact Heps).
  assert (Hhalf : Qlt (eps / 2)%Q eps)
    by exact (S02_CauchyComplete.q_half_lt eps H0lt).
  assert (Hcmp0 : Qcompare (eps / 2)%Q eps = Lt)
    by (apply Qlt_alt; exact Hhalf).
  assert (Hsub : (eps - (q + - q))%Q == eps) by ring.
  assert (Hcmp : Qcompare (eps / 2)%Q (eps - (q + - q)) = Lt).
  { assert (Hc1 : Qcompare (eps / 2)%Q (eps - (q + - q)) = Qcompare (eps / 2)%Q eps).
    { exact (Qcompare_comp (eps / 2)%Q (eps / 2)%Q (Qeq_refl (eps / 2)%Q)
                           (eps - (q + - q))%Q eps Hsub). }
    rewrite Hc1. exact Hcmp0. }
  unfold S02_CauchyComplete.QltT, Qlt_bool. rewrite Hcmp. reflexivity.
Qed.

(* 实例件一：柯西完备性的原始 eps/N 形包装（dist 收敛包装）。     *)
(*   从柯西假设直接取得极限 l 及其双向 eps/N 夹逼——语句面不再    *)
(*   出现 real_lim 包装层，下游拿到的即是逐 eps 见证形。          *)
Theorem aba_cauchy_limit_raw :
  forall (u : nat -> S02_CauchyComplete.Real),
    (forall eps : Q, S02_CauchyComplete.QltT 0%Q eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        S01_BaseRing.And
          (S02_CauchyComplete.real_lt
             (S02_CauchyComplete.real_plus (u m) (S02_CauchyComplete.real_opp (u n)))
             (S02_CauchyComplete.real_const eps))
          (S02_CauchyComplete.real_lt
             (S02_CauchyComplete.real_plus (u n) (S02_CauchyComplete.real_opp (u m)))
             (S02_CauchyComplete.real_const eps)))) ->
    sigT (fun l : S02_CauchyComplete.Real =>
      forall eps : Q, S02_CauchyComplete.QltT 0%Q eps ->
        sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
          S01_BaseRing.And
            (S02_CauchyComplete.real_lt (u n)
               (S02_CauchyComplete.real_plus l (S02_CauchyComplete.real_const eps)))
            (S02_CauchyComplete.real_lt
               (S02_CauchyComplete.real_plus l (S02_CauchyComplete.real_opp (S02_CauchyComplete.real_const eps)))
               (u n)))).
Proof.
  intros u Hcau.
  exact (S02_CauchyComplete.real_cauchy_complete u Hcau).
Qed.

(* 实例件二：完备性的具体应用实例——常值实数列收敛。             *)
(*   把主定理实例化到 u := fun _ => real_const q，柯西假设以     *)
(*   N := 0、阈值 eps/2 显式见证（逐点差恒 q + (−q)，            *)
(*   projT1 逐点展开照 S02:982 判例），真行使主定理本体。         *)
Theorem aba_const_seq_convergent :
  forall (q : Q),
    sigT (fun l : S02_CauchyComplete.Real =>
      S02_CauchyComplete.real_lim
        (fun _ : nat => S02_CauchyComplete.real_const q) l).
Proof.
  intro q.
  apply (S02_CauchyComplete.real_cauchy_complete
           (fun _ : nat => S02_CauchyComplete.real_const q)).
  intros eps Heps.
  assert (HhalfT : S02_CauchyComplete.QltT 0%Q (eps / 2)%Q).
  { apply S02_CauchyComplete.Qlt_to_QltT.
    apply Qlt_shift_div_l;
      [ reflexivity
      | simpl; apply S02_CauchyComplete.QltT_to_Qlt; exact Heps ]. }
  assert (Hkey : forall k : nat,
    S02_CauchyComplete.QltT (eps / 2)%Q
      (projT1 (S02_CauchyComplete.real_const eps) k
       - projT1
           (S02_CauchyComplete.real_plus
              (S02_CauchyComplete.real_const q)
              (S02_CauchyComplete.real_opp (S02_CauchyComplete.real_const q))) k)%Q).
  { intro k.
    (* projT1 (real_const eps) k ≡ eps、projT1 (real_plus ...) k ≡ q + (−q)   *)
    (* 皆定义性归约（real_const_proj 本身即 reflexivity 判例），故逐点目标      *)
    (* 经转换检查直接交给 Q 层辅助件闭合。                                     *)
    exact (aba_qlt_eps_sub q eps Heps). }
  exists 0%nat. intros m n Hm Hn. split.
  - exists (eps / 2)%Q. split.
    + exact HhalfT.
    + exists 0%nat. intros k Hk. exact (Hkey k).
  - exists (eps / 2)%Q. split.
    + exact HhalfT.
    + exists 0%nat. intros k Hk. exact (Hkey k).
Qed.

(* ============================================================ *)
(* §2 裸奔位二（S06 attention_is_gibbs）使用面特化              *)
(*   实例定理把「softmax = Boltzmann 记号形」特化到原始接口      *)
(*   基元形：softmax z s == e^(−z_s) · Z^(−1)（Gibbs 规范式），  *)
(*   语句面不再出现 boltzmann_dist_attn／boltzmann_factor／     *)
(*   Z_thermo 等 S06 节内缩写——真行使主定理本体。               *)
(* ============================================================ *)

Theorem aba_gibbs_softmax_explicit :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
    forall (Hsum : forall f : @S RI SS -> @R RI,
              (forall s : @S RI SS, @lt RI (@zero RI) (f s)) ->
              @lt RI (@zero RI) (@sum_over_S RI SS SO f)),
      forall (D : @R RI) (D_pos : @lt RI (@zero RI) D)
             (energy z : @S06_DiffSamplingGibbs.logits RI SS),
        (@Id (@R RI) (@inv_pos RI D D_pos) (@one RI)) ->
        (forall s : @S RI SS, @Id (@R RI) (energy s) (@opp RI (z s))) ->
        (@Id (@R RI)
             (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
             (@S06_DiffSamplingGibbs.partition_function RI SS SO z)) ->
        forall s : @S RI SS,
          @Id (@R RI)
              (@S06_DiffSamplingGibbs.softmax RI SS SO Hsum z s)
              (@mult RI
                 (@exp_neg RI (@opp RI (z s)))
                 (@inv_pos RI
                    (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                    (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z))).
Proof.
  intros RI SS SO Hsum D D_pos energy z HD Henergy HZ s.
  pose proof (@S06_DiffSamplingGibbs.attention_is_gibbs
                RI SS SO Hsum D D_pos energy z HD Henergy HZ s) as HG.
  (* HG : Id (softmax Hsum z s) (boltzmann_dist_attn Hsum D D_pos energy s) *)
  unfold S06_DiffSamplingGibbs.boltzmann_dist_attn,
         S06_DiffSamplingGibbs.boltzmann_factor in HG.
  rewrite HD in HG.
  assert (Hml : @Id (@R RI) (@mult RI (@one RI) (energy s)) (energy s))
    by exact (id_trans (mult_comm (@one RI) (energy s)) (mult_one (energy s))).
  rewrite Hml in HG.
  rewrite (Henergy s) in HG.
  assert (Hie : @Id (@R RI)
      (@inv_pos RI
         (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
         (@S06_DiffSamplingGibbs.Z_thermo_pos RI SS SO Hsum D D_pos energy))
      (@inv_pos RI
         (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
         (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z)))
    by exact (inv_pos_ext
                (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
                (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                (@S06_DiffSamplingGibbs.Z_thermo_pos RI SS SO Hsum D D_pos energy)
                (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z)
                HZ).
  rewrite Hie in HG.
  (* HG : Id (softmax ...) (mult (inv ...) (exp_neg (opp (z s))))——换序即得 Gibbs 规范式 *)
  exact (id_trans HG
           (id_sym (mult_comm (@exp_neg RI (@opp RI (z s)))
                              (@inv_pos RI
                                 (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                                 (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z))))).
Qed.

(* ============================================================ *)
(* 尾舱：公理审计面（跨件 qualified 直审 ＋ 自审）               *)
(*   判读判据：以下 6 条输出均须为 Closed under the global       *)
(*   context。前三条为对上游裸奔主定理的直审（Z 规格书跨件追审   *)
(*   形态——裸奔 Top #1/#2 主张就此进入随编译自动核验面）；       *)
(*   后三条为对本件实例语句的自审（PA≥1 下限之上）。             *)
(* ============================================================ *)
Print Assumptions S02_CauchyComplete.real_cauchy_complete.
Print Assumptions S06_DiffSamplingGibbs.attention_is_gibbs.
Print Assumptions S06_DiffSamplingGibbs.attention_is_gibbs_temp.
Print Assumptions aba_cauchy_limit_raw.
Print Assumptions aba_const_seq_convergent.
Print Assumptions aba_gibbs_softmax_explicit.
