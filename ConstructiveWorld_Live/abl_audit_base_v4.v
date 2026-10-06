(* ===================================================================== *)
(*  abl_audit_base_v4.v —— 审计载体扩容 v4·链式复合载体件                    *)
(* ===================================================================== *)
(*  使命: Z 裸奔面 Top3 行两名的链式复合闭合（Z §④候选 1 的 S06 链施工件：    *)
(*        BX 登记候选 1「只完成前半段原料」、BZ 登记「三链闭合留待并件」，     *)
(*        本件即闭合位）。载体语句两件，链式三定理一线复合：                  *)
(*        ① abd_tv_contraction_twice_orbit——单步 TV 收缩主定理               *)
(*          （attention_tv_contraction）×保持性二件                          *)
(*          （attention_step_normalized/attention_step_nonneg）的两次迭代    *)
(*          复合推论沿轨道点一般形：对任意归一化非负 w，                     *)
(*          tv(step(step w), p_attn) ≤ (1−δ)·(1−δ)·tv(w, p_attn)；           *)
(*        ② abd_iterate_converges_via_twice——两次迭代复合再接收敛主定理      *)
(*          （attention_iterate_converges）的链式复合件：同一见证 N 下，      *)
(*          n 步迭代 TV 距 < eps（收敛面）且 2+n 步迭代 TV 距                *)
(*          ≤ (1−δ)²·eps（复合面），二面单语句并载。                         *)
(*        Top4 行（S04 boltzmann_normalized/boltzmann_dist_temp_normalized） *)
(*        经核验已由 v2 件使用＋直审双覆盖（abb_boltzmann_pair_mass_two），   *)
(*        本件不重复供给，仅登记核对。                                       *)
(*  依赖: S01_BaseRing S02_CauchyComplete S03_QExp S04_RealExpLogConv        *)
(*        S05_AlignmentGRPO S06_DiffSamplingGibbs（-Q 预编译树只读引用）；    *)
(*        文尾 Stdlib Extraction（出口舱）。                                 *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 载体：语句面存在/见证全 sigT      *)
(*        （Set 层），合取用 S01_BaseRing.And（:= A*B，Set 层），             *)
(*        比较全 Id/le/lt（Set 型），无 exists/Prop 连词、无否定形书写；      *)
(*        节内 Variable 位与定理前提位全 Set 型（Id/le/lt/sigT 面）；        *)
(*        证明体全 exact/apply 显式项直交，两次复合段沿 v2 件已验链形。       *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no             *)
(*        -Q vo_local_world_unified_0930 "" abl_audit_base_v4.v              *)
(*        （独占池 audit_base_v4/，道闸≤1，单件无池内链序）。                 *)
(*  核验注: ①链上五主签名以检验 Check 实拍为准逐一调形——                    *)
(*        attention_iterate_converges 带 Hltc/Hlec 双加法兼容前提与 Hdecay    *)
(*        几何衰减见证前提；attention_tv_contraction 仅带 Hd1 不带 Hd0；      *)
(*        attention_step_normalized 不带 Hmin/Hdb。②iterate 系 S01 自有      *)
(*        Fixpoint（按 n 归纳，S 侧 = f (iterate f n' x)），故               *)
(*        iterate f (2+n) x ≡ f (f (iterate f n x)) 定义性成立，             *)
(*        复合面轨道换位经转换检查直交。③abd_ 前缀全树 grep 零命中。          *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.

(* ============================================================ *)
(* §1 载体语句舱·复合第一段                                       *)
(*    单步 TV 收缩 × 保持性二件 ⟹ 两次迭代复合（轨道点一般形）      *)
(* ============================================================ *)

Section AbdTvTwiceOrbit.

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

Variable sum_pos_preserved : forall f : S -> R,
                             (forall s : S, lt zero (f s)) ->
                             lt zero (sum_over_S f).
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : @logits RI SS.
Variable transition : S -> S -> R.
Variable delta : R.
Variable Hrow : forall s : S,
  Id (sum_over_S (fun s' : S => transition s s')) one.
Variable Hdb : forall s s' : S,
  Id (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s)
           (transition s s'))
     (mult (boltzmann_dist_attn sum_pos_preserved D D_pos energy s')
           (transition s' s)).
Variable Hd0 : lt zero delta.
Variable Hd1 : lt delta one.
Variable Hmin : forall s s' : S,
  le (mult delta (boltzmann_dist_attn sum_pos_preserved D D_pos energy s'))
     (transition s s').
Variable Hltc : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Variable Hswap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable Habs : forall a : R, le zero a -> Id (abs a) a.

(* 载体件一：两次迭代复合（轨道点一般形）。对任意归一化非负 w，两次       *)
(* 注意力步后的 TV 距以 (1−δ)² 因子收缩——单步收缩主定理沿中态            *)
(* （step w）与起点 w 各行使一次，中态的归一化/非负由保持性二件供给。      *)
Theorem abd_tv_contraction_twice_orbit :
  forall w : S -> R,
  Id (sum_over_S w) one ->
  (forall s : S, le zero (w s)) ->
  le (tv_dist (attention_step transition (attention_step transition w))
              (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
     (mult (minus one delta)
           (mult (minus one delta)
                 (tv_dist w
                    (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
Proof.
  intros w Hw1 Hw2.
  apply (le_trans _
          (mult (minus one delta)
                (tv_dist (attention_step transition w)
                         (boltzmann_dist_attn sum_pos_preserved D D_pos energy))) _).
  - (* 第二步：对 (step w) 再收缩一次；中态归一化/非负由保持性二件供给 *)
    exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
             Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs
             (attention_step transition w)
             (attention_step_normalized sum_pos_preserved D D_pos energy transition
                Hrow delta Hd1 Hltc Hswap w Hw1)
             (attention_step_nonneg sum_pos_preserved D D_pos energy transition delta
                Hd0 Hd1 Hmin Hltc w Hw1 Hw2)).
  - (* 第一步因子：0 < 1−δ 入 le_mult_compat_r 放缩                     *)
    apply (le_mult_compat_r (minus one delta)
             (tv_dist (attention_step transition w)
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
             (mult (minus one delta)
                   (tv_dist w
                      (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))).
    + exact (lt_le_iff zero (minus one delta)
              (inl (one_minus_delta_pos delta Hd1 Hltc))).
    + exact (attention_tv_contraction sum_pos_preserved D D_pos energy transition
               Hrow Hdb delta Hd1 Hmin Hltc Hswap Habs w Hw1 Hw2).
Qed.

(* ============================================================ *)
(* §2 载体语句舱·复合第二段                                       *)
(*    两次迭代复合（载体件一）再接收敛主定理——链式闭合件            *)
(*    （使用 attention_iterate_converges ＋ n 步保持性二件          *)
(*      iterate_attention_normalized/iterate_attention_nonneg）    *)
(* ============================================================ *)

(* 载体件二：同一见证 N 下二面并载——                              *)
(*   收敛面：n ≥ N 时 tv(iterate n mu0, p_attn) < eps               *)
(*   （收敛主定理输出原样入位）；                                   *)
(*   复合面：n ≥ N 时 tv(iterate (2+n) mu0, p_attn)                *)
(*             ≤ (1−δ)·(1−δ)·eps——载体件一沿轨道点                  *)
(*   w := iterate n mu0 行使（其归一化/非负由 n 步保持性二件供给），  *)
(*   再以 0 < 1−δ 两级放缩到 eps。二面证体即链式三定理一线。          *)
Theorem abd_iterate_converges_via_twice :
  forall (Hlec : forall a b c d : R,
            le a b -> lt c d -> lt (plus a c) (plus b d))
         (Hdecay : forall a : R,
                     lt zero a ->
                     forall eps : R, lt zero eps ->
                     sigT (fun N : nat =>
                       lt (mult a (r_pow (minus one delta) N)) eps))
         (mu0 : S -> R),
  Id (sum_over_S mu0) one ->
  (forall s : S, le zero (mu0 s)) ->
  forall eps : R,
  lt zero eps ->
  lt zero (tv_dist mu0
             (boltzmann_dist_attn sum_pos_preserved D D_pos energy)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    S01_BaseRing.And
      (lt (tv_dist (iterate (attention_step transition) n mu0)
                   (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
          eps)
      (le (tv_dist (iterate (attention_step transition) (2 + n)%nat mu0)
                   (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
          (mult (minus one delta) (mult (minus one delta) eps)))).
Proof.
  intros Hlec Hdecay mu0 Hn Hnn eps Heps Hinit.
  destruct (attention_iterate_converges sum_pos_preserved D D_pos energy transition
              Hrow Hdb delta Hd0 Hd1 Hmin Hltc Hlec Hswap Habs Hdecay
              mu0 Hn Hnn eps Heps Hinit) as [N0 HconvN].
  exists N0. intros n Hn0.
  split.
  - (* 收敛面：收敛主定理输出原样入位 *)
    exact (HconvN n Hn0).
  - (* 复合面：载体件一沿轨道点行使，再两级放缩到 eps                    *)
    apply (le_trans _
            (mult (minus one delta)
                  (mult (minus one delta)
                        (tv_dist (iterate (attention_step transition) n mu0)
                                 (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))) _).
    + exact (abd_tv_contraction_twice_orbit
               (iterate (attention_step transition) n mu0)
               (iterate_attention_normalized sum_pos_preserved D D_pos energy transition
                  Hrow delta Hd1 Hltc Hswap mu0 n Hn)
               (iterate_attention_nonneg sum_pos_preserved D D_pos energy transition
                  Hrow delta Hd0 Hd1 Hmin Hltc Hswap mu0 n Hn Hnn)).
    + apply (le_mult_compat_r (minus one delta)
               (mult (minus one delta)
                     (tv_dist (iterate (attention_step transition) n mu0)
                              (boltzmann_dist_attn sum_pos_preserved D D_pos energy)))
               (mult (minus one delta) eps)).
      * exact (lt_le_iff zero (minus one delta)
                  (inl (one_minus_delta_pos delta Hd1 Hltc))).
      * apply (le_mult_compat_r (minus one delta)
                 (tv_dist (iterate (attention_step transition) n mu0)
                          (boltzmann_dist_attn sum_pos_preserved D D_pos energy)) eps).
        -- exact (lt_le_iff zero (minus one delta)
                    (inl (one_minus_delta_pos delta Hd1 Hltc))).
        -- exact (lt_le_iff
                    (tv_dist (iterate (attention_step transition) n mu0)
                             (boltzmann_dist_attn sum_pos_preserved D D_pos energy))
                    eps (inl (HconvN n Hn0))).
Qed.

End AbdTvTwiceOrbit.

(* ============================================================ *)
(* §3 尾舱·假设审计（链上六面跨件直审＋本件两载体自审）              *)
(*    判读判据：八条全输出 Closed under the global context。         *)
(*    前 6 条＝S06 收敛链六面（单步收缩/单步保持性二件/收敛主定理/    *)
(*    n 步保持性二件）的跨件追审——其中六面此前全树直审为 0（Top3 行）；*)
(*    后 2 条＝本件两载体自审。载体件二的假设面沿传递依赖自动包含     *)
(*    载体件一与链上六面的公理面并集（复合审计单调性，Z §④候选 1）。  *)
(* ============================================================ *)

Print Assumptions S06_DiffSamplingGibbs.attention_tv_contraction.
Print Assumptions S06_DiffSamplingGibbs.attention_step_normalized.
Print Assumptions S06_DiffSamplingGibbs.attention_step_nonneg.
Print Assumptions S06_DiffSamplingGibbs.attention_iterate_converges.
Print Assumptions S06_DiffSamplingGibbs.iterate_attention_normalized.
Print Assumptions S06_DiffSamplingGibbs.iterate_attention_nonneg.
Print Assumptions abd_tv_contraction_twice_orbit.
Print Assumptions abd_iterate_converges_via_twice.

(* ============================================================ *)
(* §4 出口舱：载体兼任提取端口（G3：提取面零魔数）                   *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abd_tv_contraction_twice_orbit abd_iterate_converges_via_twice.
