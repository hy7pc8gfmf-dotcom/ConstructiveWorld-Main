(* ============================================================ *)
(* UpAblA2_LoInflation.v —— k ∝ lo⁻² 膨胀律定理（四倍律与反单调）        *)
(*                                                            *)
(* 使命：本件形式化 lo 膨胀律：固定初始偏差 TV₀ 与预算 budget，          *)
(*  Doeblin 常数 lo 减半 ⟹ 混合选择器所需步数 k 的显式上界精确翻四倍——   *)
(*  ub(lo/2) == 4·ub(lo)（Id 层面精确，无损耗；由 k 上界 ∝ 1/δ* =        *)
(*  1/lo² 直接导出，1/(lo/2)² = 4/lo²）；且该上界对 lo² 反单调           *)
(*  （lo 越小上界越大）。                                                *)
(*  定位：论文7 §2.3 定性对照（lo → 0 时 δ* → 0、收缩因子 1−δ* → 1、     *)
(*  Doeblin 界混合时间无界）的库内定量上界侧推论。onset 边界注记：        *)
(*  winner-takes-all 的「不可混合」下界方向（TV 的下界估计）本件不承载，  *)
(*  下界方向仍开放，与论文7 §2.3 末注一致。                              *)
(*                                                            *)
(* 内容总览（§1 抽象膨胀律，Section LoInflation，接口层）：               *)
(*  · loi_ds2_scale：(lo/2)²·4 == lo²（δ* 减半律，精确 Id）；            *)
(*  · loi_ds2_le_ds / loi_ds2_lt_one：(lo/2)² ≤ lo² 与 (lo/2)² < 1；     *)
(*  · loi_ub2_quad：ub(lo/2) == 4·ub(lo)（核心四倍律，精确 Id）；        *)
(*  · loi_lo_inflation：双配置预算达成（κ := 1−lo² 与                    *)
(*    κ₂ := 1−(lo/2)²，由 ums_pow_tail 给出）与支配界：减半配置选择器    *)
(*    返回步数 k₂ 满足 k₂ > 4·ub(lo) = 4·TV₀/(lo²·budget)；              *)
(*  · loi_ub_antitone：lo² 单调 ⟹ k-上界反单调。                         *)
(* 内容总览（§2 注意力实例化，Section LoInflationAttn）：                 *)
(*  · loi_attn_ds_lt_one：δ* = lo·lo < 1（由 bs_delta_star_lt_one）；     *)
(*  · loi_attention_inflation：注意力核 TV 形预算达成与支配界（同一       *)
(*    k 满足 TV(T^k μ,T^k ν) < budget 且 k > TV₀/(δ*·budget)）；          *)
(*  · loi_attention_halving_quad：注意力核上 ub(lo/2) == 4·ub(lo)        *)
(*    （loi_ub2_quad 在 TV₀ := tv μ ν 的实例化）；                        *)
(*  · loi_attention_inflation_half：loi_lo_inflation 在注意力 TV₀/lo     *)
(*    的全参实例化（结论为 r_pow 形态的双配置合取）。                    *)
(*                                                            *)
(* 来源参照：AttnDoeblin.v BoundedSoftmax 节（lo := expf(invT·(−Δ))、     *)
(*  delta_star := lo·lo、bs_delta_star_lt_one）；UpReqMixingTime.v       *)
(*  mix_k_select 线性代价结构（k ≈ TV₀/((1−κ)·budget)，κ := 1−δ*）；     *)
(*  UpReqUMixSelect.v ums_pow_tail（Arch 输入 TV₀·inv(w·budget) 的       *)
(*  显式入口）。                                                         *)
(*                                                            *)
(* 口径注记：ums_pow_tail 的 Arch 输入 x := TV₀·inv(w·budget) 与          *)
(*  ums_k_select 内部应用点逐字同型——故本件 projT1 给出的步数即          *)
(*  选择器在同 Arch 见证下的返回步数（同型 congruence）。                *)
(*                                                            *)
(* 诚实接口（Variable，与 AttnDoeblin/UpReqUMixSelect 一致）：Arch 前提   *)
(*  取 ums_k_select 的 nat-尺度 ums_scale 形态；本件零新增接口参数。      *)
(*                                                            *)
(* 依赖：CW_ConstructiveWorld_219（S01 接口/环律、S04 r_pow、S06 tv）；  *)
(*  AttnDoeblin（BoundedSoftmax 全集、bs_delta_star_lt_one）；           *)
(*  UpReqUMixSelect（ums_pow_tail/ums_scale/ums_le_plus_r/ums_mult_one_l）。*)
(* 对标：mathlib Doeblin 条件混合时间定量上界的构造性 Set 层对应物。     *)
(*                                                            *)
(* 构造性注记：语句面全 Set 层（量词 R/nat；比较全接口 lt/le Set 字段；  *)
(*  sigT + And 承载，同 AttnDoeblin.v 的 real_expf_realizable 形态）；    *)
(*  零经典逻辑；零新增公理，前提全为 Set 层显式证书值参；                *)
(*  Print Assumptions 预期全 Closed；主定理 Defined 可提取。             *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。           *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import UpReqUMixSelect.

(* ================= §1 抽象膨胀律（接口层） ================= *)

Section LoInflation.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let one := @one RI.
Let zero := @zero RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.

(* 接口参数：混合 lt+le 加法保序（与 UpReqUMixSelect 同名参数，          *)
(*   供 ums_pow_tail 应用；本节内显式声明，不提升出节）                  *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ---- 固定参量：TV₀ / budget（全文固定） ---- *)
Variable TV0 : R.
Variable Htv0 : le zero TV0.
Variable budget : R.
Variable Hbudget : lt zero budget.

(* ---- 膨胀参数：lo（注意力实例里 = expf(−Δ/T)） ---- *)
Variable lo : R.
Variable Hlo0 : lt zero lo.
Variable Hds1 : lt (mult lo lo) one.   (* δ* < 1：Doeblin 证书 *)

(* Arch 前提（ums_k_select 的形态：le 前提 + nat-尺度 ums_scale 形） *)
Variable Harch : forall x : R, le zero x ->
  sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one)).

(* ---- 缩放常量：two / four 与逆元 ---- *)
Let two := plus one one.
Let Htwo0 : lt zero two := plus_positive one one one_pos one_pos.
Let inv2 := inv_pos two Htwo0.
Let four := plus two two.
Let Hfour0 : lt zero four := plus_positive two two Htwo0 Htwo0.
Let inv4 := inv_pos four Hfour0.

(* ---- 两配置：lo 与 lo/2；δ* := lo² 与 δ*₂ := (lo/2)² = δ*⁄4 ---- *)
Let lo_half := mult lo inv2.
Let ds := mult lo lo.
Let ds2 := mult lo_half lo_half.
Let kap := minus one ds.
Let kap2 := minus one ds2.

(* ---- 两配置的 Arch 输入 = 选择器显式 k-上界 ---- *)
Let Hds0 : lt zero ds := mult_positive lo lo Hlo0 Hlo0.
Let Hwb : lt zero (mult ds budget) :=
  mult_positive ds budget Hds0 Hbudget.
Let ub := mult TV0 (inv_pos (mult ds budget) Hwb).
Let Hlohalf0 : lt zero lo_half :=
  mult_positive lo inv2 Hlo0 (inv_pos_pos two Htwo0).
Let Hds2_0 : lt zero ds2 := mult_positive lo_half lo_half Hlohalf0 Hlohalf0.
Let Hwb2 : lt zero (mult ds2 budget) :=
  mult_positive ds2 budget Hds2_0 Hbudget.
Let ub2 := mult TV0 (inv_pos (mult ds2 budget) Hwb2).

(* ---------- 基础序引理 ---------- *)

(* 1 ≤ 4（1 ≤ 2 ≤ 4） *)
Lemma loi_le_one_four : le one four.
Proof.
  apply (le_trans one (plus one one) four).
  - exact (ums_le_plus_r one one (lt_le_iff zero one (inl one_pos))).
  - exact (ums_le_plus_r two two
             (le_id_l zero (plus zero zero) two
                (id_sym (plus_zero zero))
                (le_plus_compat zero one zero one
                   (lt_le_iff zero one (inl one_pos))
                   (lt_le_iff zero one (inl one_pos))))).
Qed.

(* ---------- 环律恒等式（接口层 Id 链式，不经 ring） ---------- *)

(* 2·inv2 == 1 *)
Lemma loi_inv2_two : Id (mult two inv2) one.
Proof.
  exact (inv_pos_correct two Htwo0).
Qed.

(* inv2·four == two（= 4/2） *)
Lemma loi_inv2_four_two : Id (mult inv2 four) two.
Proof.
  apply (id_trans (mult_comm inv2 four)).
  apply (id_trans (mult_plus_distr_r two two inv2)).
  apply (id_trans (id_cong2 plus
             (inv_pos_correct two Htwo0)
             (inv_pos_correct two Htwo0))).
  exact (id_refl : Id (plus one one) two).
Qed.

(* 逆元外延：a == b（皆正）⟹ inv a == inv b *)
Lemma loi_inv_wd : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  Id a b -> Id (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hab.
  apply (mult_cancel_l b (inv_pos a Ha) (inv_pos b Hb) Hb).
  exact (id_trans
           (id_trans
              (id_cong (fun x => mult x (inv_pos a Ha)) (id_sym Hab))
              (inv_pos_correct a Ha))
           (id_sym (inv_pos_correct b Hb))).
Qed.

(* ---------- ① δ* 减半律：(lo/2)²·4 == lo² ---------- *)
Lemma loi_ds2_scale : Id (mult four ds2) ds.
Proof.
  assert (H1 : Id (mult four lo_half) (mult lo two)).
  { exact (id_trans (mult_assoc four lo inv2)
           (id_trans
              (id_cong2 mult (mult_comm four lo) (id_refl : Id inv2 inv2))
           (id_trans (id_sym (mult_assoc lo four inv2))
           (id_cong (fun x => mult lo x)
              (id_trans (mult_comm four inv2) loi_inv2_four_two))))). }
  assert (H2 : Id (mult four (mult lo_half lo_half))
                  (mult (mult four lo_half) lo_half)).
  { exact (mult_assoc four lo_half lo_half). }
  assert (H3 : Id (mult (mult four lo_half) lo_half)
                  (mult (mult lo two) lo_half)).
  { exact (id_cong2 mult H1 (id_refl : Id lo_half lo_half)). }
  assert (H4 : Id (mult (mult lo two) lo_half)
                  (mult (mult (mult lo two) lo) inv2)).
  { exact (mult_assoc (mult lo two) lo inv2). }
  assert (H5 : Id (mult (mult (mult lo two) lo) inv2)
                  (mult (mult (mult lo lo) two) inv2)).
  { exact (id_trans
             (id_cong2 mult (id_sym (mult_assoc lo two lo))
                             (id_refl : Id inv2 inv2))
             (id_cong2 mult
                (id_trans (id_cong (fun x => mult lo x) (mult_comm two lo))
                          (mult_assoc lo lo two))
                (id_refl : Id inv2 inv2))). }
  assert (H6 : Id (mult (mult (mult lo lo) two) inv2) ds).
  { exact (id_trans (id_sym (mult_assoc (mult lo lo) two inv2))
           (id_trans (id_cong (fun x => mult (mult lo lo) x) loi_inv2_two)
                     (mult_one (mult lo lo)))). }
  exact (id_trans (id_trans (id_trans H2 H3) H4) (id_trans H5 H6)).
Qed.

(* (lo/2)² ≤ lo²（经 1 ≤ 4 与 loi_ds2_scale） *)
Lemma loi_ds2_le_ds : le ds2 ds.
Proof.
  apply (le_trans ds2 (mult ds2 one) ds).
  - exact (le_id_r ds2 ds2 (mult ds2 one)
             (id_sym (mult_one ds2)) (le_refl ds2)).
  - apply (le_trans (mult ds2 one) (mult ds2 four) ds).
    + exact (le_mult_compat_r ds2 one four
               (lt_le_iff zero ds2 (inl Hds2_0)) (loi_le_one_four)).
    + exact (le_id_l (mult ds2 four) ds ds
               (id_trans (mult_comm ds2 four) loi_ds2_scale) (le_refl ds)).
Qed.

(* δ*₂ = (lo/2)² < 1（κ₂ 证书） *)
Lemma loi_ds2_lt_one : lt ds2 one.
Proof.
  exact (le_lt_trans ds2 ds one loi_ds2_le_ds Hds1).
Qed.


(* ---------- 核心四倍律：ub(lo/2) == 4·ub(lo) ---------- *)
Lemma loi_ub2_quad : Id ub2 (mult four ub).
Proof.
  assert (Hsplit : Id (mult ds budget) (mult four (mult ds2 budget))).
  { exact (id_trans (id_cong2 mult (id_sym loi_ds2_scale)
                                   (id_refl : Id budget budget))
                    (id_sym (mult_assoc four ds2 budget))). }
  assert (Hbinv : Id (inv_pos (mult ds budget) Hwb)
                     (mult inv4 (inv_pos (mult ds2 budget) Hwb2))).
  { exact (id_trans
             (loi_inv_wd (mult ds budget)
                         (mult four (mult ds2 budget))
                         Hwb
                         (mult_positive four (mult ds2 budget)
                            Hfour0 Hwb2)
                         Hsplit)
             (inv_pos_mult_distr four (mult ds2 budget)
                                 Hfour0 Hwb2)). }
  assert (Hub' : Id ub (mult inv4 ub2)).
  { exact (id_trans (id_cong (fun x => mult TV0 x) Hbinv)
           (id_trans (mult_assoc TV0 inv4
                        (inv_pos (mult ds2 budget) Hwb2))
           (id_trans
              (id_cong2 mult (mult_comm TV0 inv4)
                        (id_refl : Id (inv_pos (mult ds2 budget) Hwb2)
                                      (inv_pos (mult ds2 budget) Hwb2)))
              (id_sym (mult_assoc inv4 TV0
                         (inv_pos (mult ds2 budget) Hwb2)))))). }
  assert (Hfin : Id (mult four (mult inv4 ub2)) ub2).
  { exact (id_trans (mult_assoc four inv4 ub2)
           (id_trans (id_cong2 mult
                        (inv_pos_correct four Hfour0)
                        (id_refl : Id ub2 ub2))
                     (ums_mult_one_l ub2))). }
  exact (id_sym (id_trans (id_cong (fun x => mult four x) Hub') Hfin)).
Qed.

(* ---------- 膨胀律：双配置预算达成 + 四倍支配界 ---------- *)
(* k₁ 达成 κ^k₁·TV₀ < budget（κ := 1−lo²）；k₂ 达成 κ₂^k₂·TV₀ < budget  *)
(* （κ₂ := 1−(lo/2)²）；且 k₂ > 4·ub(lo) = 4·TV₀/(lo²·budget)——          *)
(* 即固定 TV₀/budget 下 lo 减半使选择器所需 k 的上界精确翻四倍。         *)
Theorem loi_lo_inflation :
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (r_pow kap k1) TV0) budget)
        (And (lt (mult (r_pow kap2 k2) TV0) budget)
             (lt (mult four ub) (ums_scale k2 one))))).
Proof.
  assert (Hub : le zero ub).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds budget) Hwb))
             (mult TV0 (inv_pos (mult ds budget) Hwb))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult ds budget) Hwb))
                (mult_zero (inv_pos (mult ds budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds budget) Hwb)
                (lt_le_iff zero (inv_pos (mult ds budget) Hwb)
                             (inl (inv_pos_pos (mult ds budget) Hwb)))
                Htv0)). }
  assert (Hub2 : le zero ub2).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds2 budget) Hwb2))
             (mult TV0 (inv_pos (mult ds2 budget) Hwb2))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult ds2 budget) Hwb2))
                (mult_zero (inv_pos (mult ds2 budget) Hwb2))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds2 budget) Hwb2)
                (lt_le_iff zero (inv_pos (mult ds2 budget) Hwb2)
                             (inl (inv_pos_pos (mult ds2 budget) Hwb2)))
                Htv0)). }
  destruct (Harch ub Hub) as [N1 HN1].
  destruct (Harch ub2 Hub2) as [N2 HN2].
  destruct (ums_pow_tail lt_plus_compat_lt_le kap TV0 budget ds N1 Hwb
              Hds0 Hds1
              (id_refl : Id kap (minus one ds)) Htv0
              (lt_le_iff zero budget (inl Hbudget)) HN1) as [k1 Hk1].
  pose (Hp2 := ums_pow_tail lt_plus_compat_lt_le kap2 TV0 budget ds2 N2 Hwb2
                 Hds2_0 loi_ds2_lt_one
                 (id_refl : Id kap2 (minus one ds2)) Htv0
                 (lt_le_iff zero budget (inl Hbudget)) HN2).
  exists k1. exists (projT1 Hp2). split.
  - exact Hk1.
  - split.
    + exact (projT2 Hp2).
    + exact (lt_id_l (mult four ub) ub2 (ums_scale (projT1 Hp2) one)
               (id_sym loi_ub2_quad) HN2).
Defined.

(* ---------- k-上界的反单调律 ---------- *)
(* lo² ≤ lo'² ⟹ ub(lo') ≤ ub(lo)：lo 越小（Doeblin 常数越弱），          *)
(* 选择器所需 k 的显式上界越大——onset 方向的单调定量律。                 *)
Lemma loi_ub_antitone :
  forall (lo' : R) (Htv0s : lt zero TV0)
         (Hlo2b : lt zero (mult (mult lo' lo') budget)),
  le ds (mult lo' lo') ->
  le (mult TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b)) ub.
Proof.
  intros lo' Htv0s Hlo2b Hle.
  assert (Hdsb_le : le (mult ds budget) (mult (mult lo' lo') budget)).
  { exact (le_mult_compat ds (mult lo' lo') budget Hbudget Hle). }
  assert (Hinv : le (inv_pos (mult (mult lo' lo') budget) Hlo2b)
                    (inv_pos (mult ds budget) Hwb)).
  { exact (inv_pos_le_compat (mult ds budget)
                             (mult (mult lo' lo') budget)
                             Hwb Hlo2b Hdsb_le). }
  exact (le_id_l
           (mult TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b))
           (mult (inv_pos (mult (mult lo' lo') budget) Hlo2b) TV0)
           ub
           (mult_comm TV0 (inv_pos (mult (mult lo' lo') budget) Hlo2b))
           (le_id_r
              (mult (inv_pos (mult (mult lo' lo') budget) Hlo2b) TV0)
              (mult (inv_pos (mult ds budget) Hwb) TV0)
              ub
              (mult_comm (inv_pos (mult ds budget) Hwb) TV0)
              (le_mult_compat
                 (inv_pos (mult (mult lo' lo') budget) Hlo2b)
                 (inv_pos (mult ds budget) Hwb)
                 TV0 Htv0s Hinv))).
Qed.

End LoInflation.

(* ================= §2 注意力实例化（BoundedSoftmax 核） =================
   以 UpReqAttnMixTime.v 同款参数面实例化 BoundedSoftmax 全集；
   lo := expf(invT·(−Δ))、delta_star := lo·lo（AttnDoeblin 精确无损耗）。 *)

Section LoInflationAttn.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

(* ---- BoundedSoftmax 接口全集（同 AttnDoeblin.v BoundedSoftmax 节的参数面） ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).

(* ---- 核实例（BoundedSoftmax 参数的显式实例化，同 UpReqAttnMixTime.v） ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let amt_kernel : S -> S -> R :=
  bs_kernel enum enum_nonempty temp temp_pos Delta z z_lb expf expf_pos
            expf_mono_le sum_eq_list.

(* ---- 缩放常量与两配置（同 §1 形） ---- *)
Let two := plus one one.
Let Htwo0 : lt zero two := plus_positive one one one_pos one_pos.
Let inv2 := inv_pos two Htwo0.
Let four := plus two two.
Let Hfour0 : lt zero four := plus_positive two two Htwo0 Htwo0.
Let lo_half_star := mult lo inv2.

Let Hlo0 : lt zero lo := expf_pos (mult invT (opp Delta)).
Let ds_star_pos : lt zero delta_star := mult_positive lo lo Hlo0 Hlo0.
Let Hlohalf0 : lt zero lo_half_star :=
  mult_positive lo inv2 Hlo0 (inv_pos_pos two Htwo0).
Let Hds2s0 : lt zero (mult lo_half_star lo_half_star) :=
  mult_positive lo_half_star lo_half_star Hlohalf0 Hlohalf0.

(* δ* < 1（由 bs_delta_star_lt_one 直接推得） *)
Lemma loi_attn_ds_lt_one : lt delta_star one.
Proof.
  exact (bs_delta_star_lt_one temp temp_pos Delta Delta_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* ---------- 注意力核 TV 形膨胀律 ---------- *)
(* 同一 Arch 见证下选择器返回步数 k 满足：                              *)
(*   TV(T^k μ, T^k ν) < budget  且  k > TV₀/(δ*·budget)（支配界）。      *)
Theorem loi_attention_inflation :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall (budget : R) (Hbudget : lt zero budget),
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    And (lt (tv (@u_titer RI SS SO amt_kernel k mu)
                (@u_titer RI SS SO amt_kernel k nu)) budget)
        (lt (mult (tv mu nu)
                  (inv_pos (mult delta_star budget)
                     (mult_positive delta_star budget ds_star_pos Hbudget)))
            (ums_scale k one))).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  assert (Htvnn : le zero (tv mu nu)) by exact (tv_dist_nonneg mu nu).
  pose (HwbA := mult_positive delta_star budget ds_star_pos Hbudget).
  assert (Hub : le zero (mult (tv mu nu)
                          (inv_pos (mult delta_star budget) HwbA))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult delta_star budget) HwbA))
             (mult (tv mu nu) (inv_pos (mult delta_star budget) HwbA))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult delta_star budget) HwbA))
                (mult_zero (inv_pos (mult delta_star budget) HwbA))))
             (le_mult_compat_weak zero (tv mu nu)
                (inv_pos (mult delta_star budget) HwbA)
                (lt_le_iff zero (inv_pos (mult delta_star budget) HwbA)
                             (inl (inv_pos_pos (mult delta_star budget)
                                    HwbA)))
                Htvnn)). }
  destruct (Harch (mult (tv mu nu)
                     (inv_pos (mult delta_star budget) HwbA)) Hub) as [N HN].
  pose (Hp := ums_pow_tail bs_lpc (minus one delta_star) (tv mu nu) budget
                 delta_star N HwbA ds_star_pos loi_attn_ds_lt_one
                 (id_refl : Id (minus one delta_star)
                               (minus one delta_star))
                 Htvnn (lt_le_iff zero budget (inl Hbudget)) HN).
  exists (projT1 Hp). split.
  - apply (le_lt_trans _
             (mult (r_pow (minus one delta_star) (projT1 Hp)) (tv mu nu))
             budget).
    + exact (bounded_softmax_tv_iter enum enum_nonempty temp temp_pos
               Delta Delta_pos z z_lb z_ub expf expf_pos expf_zero
               expf_plus expf_mono_lt expf_mono_le bs_swap bs_abs bs_lpc
               sum_eq_list (projT1 Hp) mu nu Hmu Hnu).
    + exact (projT2 Hp).
  - exact HN.
Defined.

(* ---------- 注意力核上的精确四倍律 ---------- *)
(* TV₀ := tv μ ν 固定、budget 固定：ub(lo/2) == 4·ub(lo)（Id）。         *)
Theorem loi_attention_halving_quad :
  forall (mu nu : S -> R) (budget : R) (Hbudget : lt zero budget),
  Id (mult (tv mu nu)
         (inv_pos (mult (mult lo_half_star lo_half_star) budget)
                  (mult_positive (mult lo_half_star lo_half_star) budget
                     Hds2s0 Hbudget)))
     (mult four
        (mult (tv mu nu)
           (inv_pos (mult delta_star budget)
              (mult_positive delta_star budget ds_star_pos Hbudget)))).
Proof.
  intros mu nu budget Hbudget.
  exact (loi_ub2_quad (tv mu nu) budget Hbudget lo Hlo0).
Qed.

(* ---------- loi_lo_inflation 在注意力 TV₀/lo 的全参实例化 ---------- *)
Theorem loi_attention_inflation_half :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall (budget : R) (Hbudget : lt zero budget),
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (r_pow (minus one delta_star) k1) (tv mu nu)) budget)
        (And (lt (mult (r_pow (minus one (mult lo_half_star lo_half_star)) k2)
                     (tv mu nu)) budget)
             (lt (mult four
                    (mult (tv mu nu)
                       (inv_pos (mult delta_star budget)
                          (mult_positive delta_star budget ds_star_pos
                             Hbudget))))
                 (ums_scale k2 one))))).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  exact (loi_lo_inflation bs_lpc (tv mu nu) (tv_dist_nonneg mu nu)
           budget Hbudget lo Hlo0 loi_attn_ds_lt_one Harch).
Qed.

End LoInflationAttn.

(* ============================================================ *)
(* 审计口：Print Assumptions（预期全 Closed）                           *)
(* ============================================================ *)

Print Assumptions loi_ds2_scale.
Print Assumptions loi_ub2_quad.
Print Assumptions loi_lo_inflation.
Print Assumptions loi_ub_antitone.
Print Assumptions loi_attention_inflation.
Print Assumptions loi_attention_halving_quad.
Print Assumptions loi_attention_inflation_half.
