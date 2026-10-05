(* ==========================================================================)
   abl_audit_base_v2.v — S06／S04 裸奢单点独立审计卷第二件
   使命：S06 单步 TV 收缩主定理（attention_tv_contraction，裸奔面 Top3）与 S04
      Boltzmann 归一化主定理（boltzmann_normalized／boltzmann_dist_temp_normalized，
      Top4 同行两名一并使用）的真使用面特化承载＋尾舱 Print Assumptions 跨件
      追审直审（Z 报告 §2 四舱制、§3.3 Top10 排位口径）。实例语句均为新语句
      非空壳：①abb_tv_contraction_twice——单步收缩经保持性引理
      （attention_step_normalized／attention_step_nonneg）两次迭代的复合推论，
      界 (1−δ)²·TV(mu)；②abb_boltzmann_pair_mass_two——基温与温度 t 两族分布
      逐点相加后的总概率质量恒等式（=2，两归一化事实的 sum_over_S_add 包装）。
   依赖清单：S01_BaseRing／S02_CauchyComplete／S03_QExp／S04_RealExpLogConv／
      S05_AlignmentGRPO／S06_DiffSamplingGibbs（-Q 预编译树只读引用）＋文尾
      Stdlib Extraction（出口舱）。
   对标行：Z 报告 §2 四舱制规格与 §3.3 裸奔面 Top10 排位表；S02 直审卷族体例
      （v1/v3 同族）。
   构造性注记：零承认语句、零经典逻辑、语句面全 Set 层（Id／le／lt／sigT 面）；
      证明体全 id_trans／id_cong／exact 显式链，无 tactic 猜测面；文尾六条
      Print Assumptions（新件两条＋跨件追审上游四条）＋Separate Extraction
      出口舱闭合。
   编译配方（独占沙箱池 audit_base_v2/，池内并发≤1，单件无池内链序）：<Live
      工具链 opam live>/bin/rocq c -native-compiler no -Q
      vo_local_world_unified_0930 ""；验证＝EXIT=0＋日志零真错＋Print
      Assumptions 全 Closed＋.vo 新于 .v。
   实测注：两上游主定理出 Section 后全参化（sum_pos_preserved／D／D_pos／
      energy／transition／行随机／细致平衡／delta／低界／四则兼容／求和交换／
      abs 兼容），本件语句按检验实录签名调形，与 Z 报告行文无出入；顶层陈述须
      Section+Context 类参包裹（裸顶层类参 evar 不闭包）。
   查重登记：顶层名 2 枚全 abb_ 新前缀，与 v1 aba_／v3 abc_ 及库内既有顶层名
      零撞零别名转发；Print Assumptions 只读直审，上游宿主零字节不动。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.

(* ============================================================ *)
(* §1 实例语句舱·Top3 位：TV 单步收缩的两次迭代复合推论             *)
(*    （使用 S06.attention_tv_contraction ＋ 保持性二件）           *)
(* ============================================================ *)

Section AbbTvTwice.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let minus := @minus RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Theorem abb_tv_contraction_twice :
  forall (sum_pos_preserved : forall f : S -> R,
                              (forall s : S, lt zero (f s)) ->
                              lt zero (sum_over_S f))
         (D : R) (D_pos : lt zero D) (energy : @logits RI SS)
         (transition : S -> S -> R),
       (forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one) ->
       (forall s s' : S,
        Id (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s)
                  (transition s s'))
           (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s')
                 (transition s' s))) ->
       forall delta : R,
       lt zero delta ->
       lt delta one ->
       (forall s s' : S,
        le (mult delta (boltzmann_dist_attn sum_pos_preserved D D_pos energy s'))
           (transition s s')) ->
       (forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
       (forall f : S -> S -> R,
        Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
           (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s')))) ->
       (forall a : R, le zero a -> Id (abs a) a) ->
       forall mu : S -> R,
       Id (sum_over_S mu) one ->
       (forall s : S, le zero (mu s)) ->
       le (tv_dist (attention_step transition (attention_step transition mu))
                   (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
          (mult (minus one delta)
                (mult (minus one delta)
                      (tv_dist mu (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
Proof.
  intros sum_pos_preserved D D_pos energy transition
         Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hswap Habs mu Hn Hnn.
  apply (le_trans _
          (mult (minus one delta)
                (tv_dist (attention_step transition mu)
                         (boltzmann_dist_attn sum_pos_preserved D D_pos energy))) _).
  - (* 第二步：对 step mu 再收缩一次（norm/nonneg 由保持性二件供给） *)
    exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
             Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs
             (attention_step transition mu)
             (attention_step_normalized sum_pos_preserved D D_pos energy transition
                Hrow delta Hd1 Hltc Hswap mu Hn)
             (attention_step_nonneg sum_pos_preserved D D_pos energy transition delta
                Hd0 Hd1 Hmin Hltc mu Hn Hnn)).
  - (* 第一步因子：(1−δ)·TV(step mu) ≤ (1−δ)·((1−δ)·TV mu) *)
    apply (le_mult_compat_r (minus one delta)
             (tv_dist (attention_step transition mu)
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
             (mult (minus one delta)
                   (tv_dist mu (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
    + exact (lt_le_iff zero (minus one delta)
              (inl (one_minus_delta_pos delta Hd1 Hltc))).
    + exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
               Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs mu Hn Hnn).
Qed.

End AbbTvTwice.

(* ============================================================ *)
(* §2 实例语句舱·Top4 位：两温族概率质量包装                       *)
(*    （使用 S04.boltzmann_normalized 与 boltzmann_dist_temp_normalized） *)
(* ============================================================ *)

Section AbbPairMass.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let minus := @minus RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Theorem abb_boltzmann_pair_mass_two :
  forall (base_loss : S -> R)
         (D : R) (D_pos : lt zero D) (Z : R) (Z_pos : lt zero Z)
         (HZ : Id Z (sum_over_S (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
         (sum_pos : forall f : S -> R,
                      (forall s : S, lt zero (f s)) ->
                      lt zero (sum_over_S f))
         (Z_temp : R -> R)
         (Z_spec : forall (t : R) (Ht : lt zero t),
                     Id (Z_temp t)
                        (sum_over_S (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
         (t : R) (Ht : lt zero t),
       Id (sum_over_S (fun s : S =>
              plus (boltzmann_dist base_loss D D_pos Z Z_pos s)
                   (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht s)))
          (plus one one).
Proof.
  intros base_loss D D_pos Z Z_pos HZ sum_pos Z_temp Z_spec t Ht.
  exact (id_trans
          (* 求和线性拆加 *)
          (sum_over_S_add (boltzmann_dist base_loss D D_pos Z Z_pos)
                          (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht))
          (* 两归一化事实分别入位 *)
          (id_trans
            (id_cong (fun x : R => plus x (sum_over_S (boltzmann_dist_temp base_loss sum_pos Z_temp Z_spec t Ht)))
                     (boltzmann_normalized base_loss D D_pos Z Z_pos HZ))
            (id_cong (fun y : R => plus one y)
                     (boltzmann_dist_temp_normalized base_loss sum_pos Z_temp Z_spec t Ht)))).
Qed.

End AbbPairMass.

(* ============================================================ *)
(* §3 尾舱·假设审计（新件两语句＋跨件追审上游四语句）               *)
(*    判读判据：六条全输出 Closed under the global context          *)
(* ============================================================ *)

Print Assumptions abb_tv_contraction_twice.
Print Assumptions abb_boltzmann_pair_mass_two.
Print Assumptions S06_DiffSamplingGibbs.attention_tv_contraction.
Print Assumptions S06_DiffSamplingGibbs.attention_iterate_converges.
Print Assumptions S04_RealExpLogConv.boltzmann_normalized.
Print Assumptions S04_RealExpLogConv.boltzmann_dist_temp_normalized.

(* ============================================================ *)
(* §4 出口舱：实例定理兼任提取端口（零 Obj.magic）                  *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abb_tv_contraction_twice abb_boltzmann_pair_mass_two.
