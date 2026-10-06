(* ==========================================================================)
   abl_lipschitz_bridge.v — Lipschitz 预算面⟹几何收缩率 显式桥（lbr_ 前缀）
   使命: 跨节桥接引理——把计算器族勘验记录中的率形态材料
     （§③率形态判定：S06 的 Lipschitz 材料 inner_lipschitz:2012/
     op_lipschitz:2570 全在 MultivariableDifferentiable 节 :1923-3000 的可微
     性预算面，与收缩收敛面 attention_tv_contraction:4380/attention_tv_iter_
     contraction:4472 异节无耦合）转化为新数学显式桥：函数 f 的 Lipschitz
     常数 L（0 ≤ L 且 L < 1）⟹ f 迭代的几何收缩率，即
       |fⁿ(x) − fⁿ(y)| ≤ Lⁿ·|x − y|（归纳构造，真 Fixpoint 迭代面）。
     三段陈述：
       Part A（Section LbrBridge，宿主无关桥本体）: 抽象载体 X:Set＋间隙面
         gap＋迭代步 step＋预算常数 L 五槽（lbr_L_nonneg/lbr_L_lt_one/
         lbr_budget/lbr_gap_nonneg/lbr_arch 诚实接口槽，后者为宿主
         r_arch_pow_attn:4432 参数位同形对应）——lbr_iter/lbr_r_pow 双 Fixpoint、
         lbr_iter_lipschitz（本桥主件：预算面⟹Lⁿ 几何迭代收缩，与收缩面
         attention_tv_iter_contraction 语句面同形态：le (gap (iter n x)
         (iter n y)) (mult (r_pow L n) (gap x y))）、lbr_r_pow_dec（NatLe
         Set 载体幂单调腿）、lbr_iter_plus（迭代加法分解，柯西序列供给面）、
         lbr_iter_step_gap_decay（相邻隙几何衰减）、lbr_step_count（精度→
         步数 sigT 计算器，attention_iterate_converges:4515 的姊妹篇形态，
         序界一律 NatLe 重述）。
       Part B（Section LbrAffine，S06 端实接）: 宿主 op_lipschitz 槽 :2570
         同形复述（lbr_op_lips_mirror——对应参数位口径，同 r_arch_pow_i 先例）
         ＋仿射步 lbr_affine_step x := c·x＋b 的两点预算构造件
         lbr_affine_budget_proj（预算面进）与 lbr_affine_iter_contraction
         （几何率面出）——可微性预算面服务收缩面的第一实例。
       Part C（Section LbrBanach，Banach 不动点定理构造性全形）: 完备性
         接口参数位 lbr_complete 与 S01 cauchy_complete_S 同形（S01:1037，
         收敛证书 lbr_clim 取 ε-刻画定义形）＋度量律槽 lbr_gap_sym/tri/zero
         （对应 smetric_sym/smetric_triangle/smetric_zero）＋clim_unique
         对应参数位。构造链: 相邻隙几何衰减⟹三角链和 lbr_iter_gap_chain⟹几何
         级数伸缩相消恒等式 lbr_geom_telescope（(1−L)·Σ_{i<k}L^i·c + L^k·c
         = c）⟹尾和上界⟹Cauchy 模数 lbr_iter_cauchy（完备性参数位使用）⟹
         lbr_banach_fixed_point（不动点存在性: 平移序列双极限＋
         lbr_clim_unique 传递）⟹lbr_fixed_point_unique（唯一性: g ≤ L·g
         ⟹ (1−L)·g ≤ 0 乘法消去）。arch 常数取 (1−L)+g₀ > 0 吸收 g₀ 可零
         性，零案例分裂；完备性面为抽象接口槽（S02 real_cauchy_complete 为
         Q 序列正则化 Real 面，与桥抽象间隙面接口不合，核验后改道登记）。
   件名与前缀: abl_lipschitz_bridge.v，lbr_ 前缀（施工前 grep 防撞: 编译树
     vo_local_world_unified_0930 与 abl_tmine04_pool 全池零命中）。
   依赖: S01_BaseRing（RealInterfaceEnhanced/NatLe/NatLe_drop/NatLe_lift/
     Set 层 And/le_mult_compat_weak/lt_le_iff/one_pos）；S02_CauchyComplete；
     S03_QExp；S04_RealExpLogConv（r_pow 形参范本）；S05_AlignmentGRPO
     （StateSpaceExtended/smetric_snorm/smult_zero）；S06_DiffSamplingGibbs
     （跨节桥对象——对应使用 op_lipschitz 参数位形态；本件零宿主出节定理直
     接引用，对应参数位口径见同族先例）；Stdlib List/PeanoNat/Extraction/
     Arith/Lia。全部 Require-only 零改动，Live/注册面/缓存根零触碰。
   构造性: 纯构造性/零公理/零 Prop 载体/Set 型（增严口径首装即合规）:
     语句面存在=sigT、合取=S01 Set 层 And（A*B）、nat 序界=NatLe（leb 判定
     型）、实面比较=RI 接口字段 lt/le（Set 层值）、步数见证=sigT nat；假设
     位零 Hypothesis/零 Prop 型；零 not 於零否定书写面。非平凡: lbr_iter/
     lbr_r_pow 双真 Fixpoint＋lbr_iter_lipschitz/lbr_r_pow_dec 真归纳。可
     提取: 尾 Separate Extraction 三 Fixpoint（真 let rec 铁证）＋尾 Print
     Assumptions 全 Closed（17 件实测）。
   后续增量（原断点续写）: ①遗产末洞修复——lbr_fixed_point_unique
     证身顶层 le_id_l a 槽误装三角链和＋id_sym 换轨反向双重伤，改 le_trans
     三角两个合取肢＋链和换形肢闭合（语句面零改动）；
     ②使用端三件: lbr_scaled_pow_nonneg（辅件）＋lbr_iter_cauchy_closed
     （对称闭式双向柯西界: ∀m n g(u_m,u_n) ≤ L^m·C＋L^n·C，无 eps 量词
     无 arch 参数位，柯西模数易用版）＋lbr_residual_calc（均匀残差
     计算器: ∀n≥N g(step u_n, u_n) < eps，无需知 Banach 点即数值定装，
     宿主 attention_iterate_converges 数值端姊妹篇）。烟测双发 5/16。
   工艺红线: term-mode 全显式实参；先写后编；道闸 ≤1；绿后清池内产物
     （.vo/.vok/.vos/.glob/.aux/提取件按卡 33 处置）；头注五字段中文。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532 && nice -19 rocq c -native-compiler no
     -Q vo_local_world_unified_0930 "" 沙箱/现役/abl_tmine04_pool/
     lipschitz_bridge/abl_lipschitz_bridge.v（ConstructiveWorld 根内执行）。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* eq→Id 桥（eq 单例消去允许入 Set 层） *)
Definition lbr_eq_id {A : Set} {x y : A} (H : x = y) : Id x y :=
  match H as H0 in (_ = z) return Id x z with
  | eq_refl => id_refl
  end.

(* ============================================================ *)
(* Part A：Lipschitz 预算面⟹几何收缩率 桥本体（宿主无关）            *)
(*   五槽诚实接口: X:Set 载体、gap 间隙面、step 迭代步、L 预算常数、   *)
(*   预算面三证书（非负/严格低于一/单步两点预算）＋间隙非负＋arch 槽。 *)
(*   桥主件 lbr_iter_lipschitz: |fⁿx − fⁿy| ≤ Lⁿ·|x−y|（归纳）。       *)
(* ============================================================ *)

Section LbrBridge.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

Variable X : Set.
Variable gap : X -> X -> R.
Variable step : X -> X.
Variable L : R.

(* 预算面双证书（S06 op_lipschitz/inner_lipschitz 参数位 And 两半的对应位） *)
Variable lbr_L_nonneg : le zero L.
Variable lbr_L_lt_one : lt L one.

(* Lipschitz 预算面: 单步两点预算（桥的左岸——预算面） *)
Variable lbr_budget : forall x y : X,
  le (gap (step x) (step y)) (mult L (gap x y)).

(* 间隙非负（收缩面 tv_dist_nonneg 的抽象位） *)
Variable lbr_gap_nonneg : forall x y : X, le zero (gap x y).

(* ===== 双 Fixpoint：几何率载体与迭代载体 ===== *)

Fixpoint lbr_r_pow (n : nat) : R :=
  match n with
  | O => one
  | Datatypes.S m => mult L (lbr_r_pow m)
  end.

Fixpoint lbr_iter (n : nat) (x : X) : X :=
  match n with
  | O => x
  | Datatypes.S m => step (lbr_iter m x)
  end.

(* arch 参数位（宿主 r_arch_pow_attn:4432 同形对应，率换 L；lbr_r_pow 为节内  *)
(*   一元几何率载体，L 已被节捕获） *)
Variable lbr_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (lbr_r_pow N)) eps).

(* ===== 基础件：单位乘与幂非负 ===== *)

Lemma lbr_gap_le_mult_one : forall x y : X,
  le (gap x y) (mult one (gap x y)).
Proof.
  intros x y.
  exact (le_id_l (gap x y) (mult one (gap x y)) (mult one (gap x y))
           (id_sym (id_trans (mult_comm one (gap x y)) (mult_one (gap x y))))
           (le_refl _)).
Qed.

Lemma lbr_r_pow_nonneg : forall n : nat, le zero (lbr_r_pow n).
Proof.
  induction n as [| n IH].
  - exact (lt_le_iff zero one (inl one_pos)).
  - simpl.
    apply (le_id_l zero (mult zero (lbr_r_pow n)) (mult L (lbr_r_pow n))).
    + exact (id_sym (id_trans (mult_comm zero (lbr_r_pow n))
                              (mult_zero (lbr_r_pow n)))).
    + apply (le_mult_compat_weak zero L (lbr_r_pow n)).
      * exact IH.
      * exact lbr_L_nonneg.
Qed.

(* ===== 几何率面：幂单调衰减（NatLe Set 载体） ===== *)

Lemma lbr_r_pow_step_dec : forall n : nat,
  le (lbr_r_pow (Datatypes.S n)) (lbr_r_pow n).
Proof.
  intro n.
  apply (le_trans _ (mult one (lbr_r_pow n)) _).
  - apply (le_mult_compat_weak L one (lbr_r_pow n)).
    + apply lbr_r_pow_nonneg.
    + apply (lt_le_iff L one). exact (inl lbr_L_lt_one).
  - apply (le_id_l (mult one (lbr_r_pow n)) (lbr_r_pow n) (lbr_r_pow n)).
    + exact (id_trans (mult_comm one (lbr_r_pow n)) (mult_one (lbr_r_pow n))).
    + apply le_refl.
Qed.

Lemma lbr_r_pow_dec : forall m n : nat,
  NatLe m n -> le (lbr_r_pow n) (lbr_r_pow m).
Proof.
  intros m n Hmn. revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - pose proof (NatLe_drop m O Hmn) as Hm0.
    assert (Hmeq : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (lbr_r_pow n) _).
      * apply lbr_r_pow_step_dec.
      * apply IH. apply (NatLe_lift m n).
        exact (proj1 (PeanoNat.Nat.leb_le m n) Emn).
    + apply Nat.leb_gt in Emn.
      pose proof (NatLe_drop m (Datatypes.S n) Hmn) as Hle.
      assert (Hmeq : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* ===== 迭代面：加法分解与步交换 ===== *)

Lemma lbr_iter_plus : forall (m n : nat) (x : X),
  Id (lbr_iter (Nat.add m n) x) (lbr_iter m (lbr_iter n x)).
Proof.
  intros m n x. induction m as [| m IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong step IH).
Qed.

Lemma lbr_iter_step_commute : forall (n : nat) (x : X),
  Id (lbr_iter n (step x)) (step (lbr_iter n x)).
Proof.
  intros n x. induction n as [| n IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong step IH).
Qed.

Lemma lbr_iter_consecutive : forall (n : nat) (x : X),
  Id (lbr_iter (Datatypes.S n) x) (lbr_iter n (step x)).
Proof.
  intros n x. simpl. exact (id_sym (lbr_iter_step_commute n x)).
Qed.

(* 乘积保序（第二因子形式，非负因子情形）: u ≤ v ⟹ w·u ≤ w·v。
   由第一因子形式 le_mult_compat_weak 经交换律换岸构成。 *)
Lemma lbr_mult_compat_r : forall u v w : R,
  le zero w -> le u v -> le (mult w u) (mult w v).
Proof.
  intros u v w Hw Huv.
  apply (le_trans _ (mult u w)).
  - apply (le_id_l (mult w u) (mult u w) (mult u w)
             (mult_comm w u) (le_refl _)).
  - apply (le_trans _ (mult v w)).
    + apply (le_mult_compat_weak u v w).
      * exact Hw.
      * exact Huv.
    + apply (le_id_l (mult v w) (mult w v) (mult w v)
               (id_sym (mult_comm w v)) (le_refl _)).
Qed.

(* ============================================================ *)
(* 桥主件: Lipschitz 预算面⟹几何迭代收缩                              *)
(*   |fⁿx − fⁿy| ≤ Lⁿ·|x−y|——与宿主收缩面 attention_tv_iter_         *)
(*   contraction 语句面同形态（gap 代 tv_dist、L 代 1−δ、step 代       *)
(*   attention_step、lbr_r_pow 代 r_pow）。基例=单位乘换形；步例=预算面  *)
(*   ＋归纳假设＋第二因子乘积保序（lbr_mult_compat_r）＋乘结合率折叠    *)
(*   （mult L (mult (r_pow n) g) 与 mult (r_pow (S n)) g 经 mult_assoc  *)
(*   定义性同项）。                                                    *)
(* ============================================================ *)

Theorem lbr_iter_lipschitz : forall (n : nat) (x y : X),
  le (gap (lbr_iter n x) (lbr_iter n y)) (mult (lbr_r_pow n) (gap x y)).
Proof.
  intros n. induction n as [| n IH]; intros x y.
  - simpl. exact (lbr_gap_le_mult_one x y).
  - simpl.
    apply (le_trans _ (mult L (gap (lbr_iter n x) (lbr_iter n y))) _).
    + apply (lbr_budget (lbr_iter n x) (lbr_iter n y)).
    + apply (le_trans _ (mult L (mult (lbr_r_pow n) (gap x y))) _).
      * apply (lbr_mult_compat_r (gap (lbr_iter n x) (lbr_iter n y))
                                 (mult (lbr_r_pow n) (gap x y)) L).
        -- exact lbr_L_nonneg.
        -- exact (IH x y).
      * apply (le_id_l (mult L (mult (lbr_r_pow n) (gap x y)))
                       (mult (mult L (lbr_r_pow n)) (gap x y))
                       (mult (lbr_r_pow (Datatypes.S n)) (gap x y))).
        -- exact (mult_assoc L (lbr_r_pow n) (gap x y)).
        -- apply le_refl.
Qed.

(* 相邻隙几何衰减: |f^{n+1}x − fⁿx| ≤ Lⁿ·|fx − x|（柯西序列供给面；
    使用桥主件，置于其后的语序修正——定义搬移，语句零改动） *)
Lemma lbr_iter_step_gap_decay : forall (n : nat) (x : X),
  le (gap (lbr_iter (Datatypes.S n) x) (lbr_iter n x))
     (mult (lbr_r_pow n) (gap (step x) x)).
Proof.
  intros n x.
  apply (le_id_l (gap (lbr_iter (Datatypes.S n) x) (lbr_iter n x))
                 (gap (lbr_iter n (step x)) (lbr_iter n x))
                 (mult (lbr_r_pow n) (gap (step x) x))).
  - exact (id_cong (fun z => gap z (lbr_iter n x)) (lbr_iter_consecutive n x)).
  - apply (lbr_iter_lipschitz n (step x) x).
Qed.

(* ===== 精度→步数 sigT 计算器（attention_iterate_converges 姊妹篇） ===== *)

Theorem lbr_step_count : forall (x y : X) (eps : R),
  lt zero (gap x y) -> lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (gap (lbr_iter n x) (lbr_iter n y)) eps).
Proof.
  intros x y eps Hg0 Hep.
  destruct (lbr_arch (gap x y) Hg0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (lbr_r_pow n) (gap x y)) _).
  - apply (lbr_iter_lipschitz n x y).
  - apply (le_lt_trans _ (mult (lbr_r_pow N) (gap x y)) _).
    + apply (le_mult_compat_weak (lbr_r_pow n) (lbr_r_pow N) (gap x y)).
      * apply lbr_gap_nonneg.
      * apply (lbr_r_pow_dec N n Hn).
    + apply (lt_id_l (mult (lbr_r_pow N) (gap x y))
                     (mult (gap x y) (lbr_r_pow N)) eps).
      * exact (mult_comm (lbr_r_pow N) (gap x y)).
      * exact HN.
Qed.

End LbrBridge.

(* ============================================================ *)
(* Part B：S06 端实接——op_lipschitz 预算面参数位对应⟹仿射收缩实例        *)
(*   宿主 op_lipschitz（S06:2570）同形复述为 lbr_op_lips_mirror（对应参数位  *)
(*   口径——宿主 Variable 不可外部使用，同 r_arch_pow_i 先例）。仿射  *)
(*   步 f x := c·x＋b 的两点预算由算子槽在 smult c 处实例化＋仿射差    *)
(*   引理（向量代数全走接口字段）＋度量-差换形（smetric_snorm 场）构成； *)
(*   几何率面出件 lbr_affine_iter_contraction 使用 Part A 桥主件。     *)
(* ============================================================ *)

Section LbrAffine.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.
Let szero := @szero RI SS.
Let splus := @splus RI SS.
Let smult := @smult RI SS.
Let sopp := @sopp RI SS.
Let smetric := @smetric RI SS.
Let snorm := @snorm RI SS.
Let smetric_snorm := @smetric_snorm RI SS.

Variable c : R.
Variable b : S.

(* 宿主算子预算面参数位同形对应（S06:2570 op_lipschitz） *)
Variable lbr_op_lips_mirror : forall L0 : S -> S,
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L0 h) szero) (mult N (smetric h szero)))).

(* 向量差（宿主 sminus 同形；本件自备零宿主定义依赖） *)
Definition lbr_sminus (u v : S) : S := splus u (sopp v).

(* ===== 向量代数小件簇（全接口字段组装，零承认） ===== *)

Lemma lbr_splus_zero_l : forall t : S, Id (splus szero t) t.
Proof.
  intro t. exact (id_trans (splus_comm szero t) (splus_zero t)).
Qed.

Lemma lbr_sopp_szero : Id (sopp szero) szero.
Proof.
  exact (id_trans (id_sym (splus_zero (sopp szero)))
                  (id_trans (splus_comm (sopp szero) szero)
                            (splus_opp szero))).
Qed.

(* 承载差消去: (−z)＋(z＋t) == t *)
Lemma lbr_splus_shift_inv : forall z t : S,
  Id (splus (sopp z) (splus z t)) t.
Proof.
  intros z t.
  apply (id_trans (splus_assoc (sopp z) z t)).
  apply (id_trans (id_cong (fun w => splus w t)
             (id_trans (splus_comm (sopp z) z) (splus_opp z)))).
  apply lbr_splus_zero_l.
Qed.

(* 逆元唯一性: z＋a == z＋b == 0 蕴含 a == b *)
Lemma lbr_splus_unique_inv : forall z a b2 : S,
  Id (splus z a) szero -> Id (splus z b2) szero -> Id a b2.
Proof.
  intros z a b2 Ha Hb.
  assert (Hca : Id a (sopp z)).
  { apply (id_trans (id_sym (lbr_splus_shift_inv z a))).
    apply (id_trans (id_cong (fun w => splus (sopp z) w) Ha)).
    apply (id_trans (splus_comm (sopp z) szero)).
    apply lbr_splus_zero_l. }
  assert (Hcb : Id b2 (sopp z)).
  { apply (id_trans (id_sym (lbr_splus_shift_inv z b2))).
    apply (id_trans (id_cong (fun w => splus (sopp z) w) Hb)).
    apply (id_trans (splus_comm (sopp z) szero)).
    apply lbr_splus_zero_l. }
  exact (id_trans Hca (id_sym Hcb)).
Qed.

(* 和取逆分配（逆元唯一性构造） *)
Lemma lbr_sopp_splus : forall u v : S,
  Id (sopp (splus u v)) (splus (sopp v) (sopp u)).
Proof.
  intros u v.
  apply (lbr_splus_unique_inv (splus u v) (sopp (splus u v))
                              (splus (sopp v) (sopp u))).
  - apply splus_opp.
  - apply (id_trans (id_sym (splus_assoc u v (splus (sopp v) (sopp u))))).
    apply (id_trans (id_cong (fun w => splus u w)
                             (splus_assoc v (sopp v) (sopp u)))).
    apply (id_trans (id_cong (fun w => splus u (splus w (sopp u)))
                             (splus_opp v))).
    apply (id_trans (id_cong (fun w => splus u w)
                             (lbr_splus_zero_l (sopp u)))).
    apply splus_opp.
Qed.

(* 中枢换轨: (u＋v)＋((−v)＋w) == u＋w（仿射差的主换轨） *)
Lemma lbr_splus_swap_mid : forall u v w : S,
  Id (splus (splus u v) (splus (sopp v) w)) (splus u w).
Proof.
  intros u v w.
  apply (id_trans (id_sym (splus_assoc u v (splus (sopp v) w)))).
  apply (id_cong (fun z => splus u z)).
  apply (id_trans (splus_assoc v (sopp v) w)).
  apply (id_trans (id_cong (fun z => splus z w) (splus_opp v))).
  apply lbr_splus_zero_l.
Qed.

(* 零向量缩放：c·0 == 0（分配律＋自差构造） *)
Lemma lbr_smult_szero : Id (smult c szero) szero.
Proof.
  assert (Hz : Id (splus (smult c szero) (smult c szero)) (smult c szero)).
  { exact (id_trans (id_sym (smult_distrib_r c szero szero))
                    (id_cong (fun w => smult c w) (lbr_splus_zero_l szero))). }
  apply (id_trans (id_sym (lbr_splus_shift_inv (smult c szero)
                                               (smult c szero)))).
  apply (id_trans (id_cong (fun w => splus (sopp (smult c szero)) w) Hz)).
  apply (id_trans (splus_comm (sopp (smult c szero)) (smult c szero))).
  apply splus_opp.
Qed.

(* 负缩放：c·(−y) == −(c·y)（分配律＋逆元唯一性） *)
Lemma lbr_smult_sopp : forall y : S,
  Id (smult c (sopp y)) (sopp (smult c y)).
Proof.
  intro y.
  assert (HA : Id (splus (smult c y) (smult c (sopp y))) szero).
  { apply (id_trans (id_sym (smult_distrib_r c y (sopp y)))).
    apply (id_trans (id_cong (fun w => smult c w) (splus_opp y))).
    exact lbr_smult_szero. }
  exact (lbr_splus_unique_inv (smult c y) (smult c (sopp y))
                              (sopp (smult c y)) HA (splus_opp (smult c y))).
Qed.

(* 度量-差换形: |u−v|₀ == |u−v|（度量由范数诱导，场字段 smetric_snorm） *)
Lemma lbr_smetric_sminus_zero : forall u v : S,
  Id (smetric (lbr_sminus u v) szero) (smetric u v).
Proof.
  intros u v.
  apply (id_trans (smetric_snorm (lbr_sminus u v) szero)).
  apply (id_trans (id_cong snorm (id_trans (id_cong (fun z => splus
                             (splus u (sopp v)) z) lbr_sopp_szero)
                             (splus_zero (splus u (sopp v)))))).
  apply (id_sym (smetric_snorm u v)).
Qed.

(* ===== 仿射步与两点预算（桥的 S06 端实接） ===== *)

Definition lbr_affine_step (x : S) : S := splus (smult c x) b.

(* 仿射差引理: f(x)−f(y) == c·(x−y)（仿射 Budget 的核心代数） *)
Lemma lbr_affine_diff : forall x y : S,
  Id (lbr_sminus (lbr_affine_step x) (lbr_affine_step y))
     (smult c (lbr_sminus x y)).
Proof.
  intros x y. unfold lbr_sminus, lbr_affine_step.
  apply (id_trans (id_cong (fun z => splus (splus (smult c x) b) z)
                           (lbr_sopp_splus (smult c y) b))).
  apply (id_trans (lbr_splus_swap_mid (smult c x) b (sopp (smult c y)))).
  apply (id_trans (id_cong (fun z => splus (smult c x) z)
                           (id_sym (lbr_smult_sopp y)))).
  exact (id_sym (smult_distrib_r c x (sopp y))).
Qed.

(* 预算面投影: 算子槽（smult c 处实例化）⟹仿射步两点预算 sigT 包 *)
Theorem lbr_affine_budget_proj : sigT (fun N : R =>
  And (le zero N)
      (forall u v : S,
        le (smetric (lbr_affine_step u) (lbr_affine_step v))
           (mult N (smetric u v)))).
Proof.
  destruct (lbr_op_lips_mirror (smult c)) as [N [HNneg HNbd]].
  exists N. split.
  - exact HNneg.
  - intros u v.
    apply (le_id_l (smetric (lbr_affine_step u) (lbr_affine_step v))
                   (smetric (lbr_sminus (lbr_affine_step u)
                                         (lbr_affine_step v)) szero)
                   (mult N (smetric u v))).
    + exact (id_sym (lbr_smetric_sminus_zero (lbr_affine_step u)
                                             (lbr_affine_step v))).
    + apply (le_trans _ (mult N (smetric (lbr_sminus u v) szero)) _).
      * apply (le_id_l (smetric (lbr_sminus (lbr_affine_step u)
                                            (lbr_affine_step v)) szero)
                       (smetric (smult c (lbr_sminus u v)) szero)
                       (mult N (smetric (lbr_sminus u v) szero))).
        -- exact (id_cong (fun z => smetric z szero) (lbr_affine_diff u v)).
        -- exact (HNbd (lbr_sminus u v)).
      * apply (le_id_l (mult N (smetric (lbr_sminus u v) szero))
                       (mult N (smetric u v)) (mult N (smetric u v))).
        -- exact (id_cong (fun z => mult N z) (lbr_smetric_sminus_zero u v)).
        -- apply le_refl.
Qed.

(* 几何率面出件: 预算面进⟹Part A 桥主件使用⟹仿射迭代几何收缩
   （与宿主收缩面 attention_tv_iter_contraction 同形态的仿射实例） *)
Theorem lbr_affine_iter_contraction : sigT (fun N : R =>
  And (le zero N)
      (forall (n : nat) (x y : S),
        le (smetric (lbr_iter S lbr_affine_step n x)
                    (lbr_iter S lbr_affine_step n y))
           (mult (lbr_r_pow N n) (smetric x y)))).
Proof.
  destruct lbr_affine_budget_proj as [N [HNneg HNbud]].
  exists N. split.
  - exact HNneg.
  - intros n x y.
    exact (@lbr_iter_lipschitz RI S smetric lbr_affine_step N HNneg HNbud n x y).
Qed.

End LbrAffine.

(* ============================================================ *)
(* Part C：Banach 不动点定理（构造性全形）——Lipschitz 预算面＋完备性    *)
(*   接口⟹不动点存在性与唯一性。接口参数位与 S01 StateSpace 度量      *)
(*   字段（smetric_sym/smetric_triangle/smetric_zero/clim_unique）与    *)
(*   cauchy_complete_S 槽形；收敛证书 lbr_clim 取 ε-刻画定义形。核心构造: *)
(*   相邻隙几何衰减⟹三角链和⟹几何级数伸缩相消恒等式                     *)
(*   (1−L)·Σ_{i<k}L^i·c + L^k·c = c ⟹Cauchy 模数（完备性参数位使用）⟹      *)
(*   极限 l；step l 的不动点性经平移序列 w_n := step(u_n) 的双极限       *)
(*   （w→l 与 w→step l）＋lbr_clim_unique 传递；唯一性经                *)
(*   g ≤ L·g ⟹ (1−L)·g ≤ 0 的乘法消去。arch 常数取 (1−L)+g₀ > 0        *)
(*   吸收 g₀ 的可零性（零案例分裂——若 x₀ 已近不动点亦同一构造通行）。    *)
(* ============================================================ *)

Section LbrBanach.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

Variable X : Set.
Variable gap : X -> X -> R.
Variable step : X -> X.
Variable L : R.

Variable lbr_L_nonneg : le zero L.
Variable lbr_L_lt_one : lt L one.
(* 严格减正字段（RW-MIX 接口前提的 TB-2 字段化归对应——S04:336/S05:2180
   墙登记：接口层无「严格从弱」产生子，消解走字段化归；本槽为该墙的
   减法形，弱于 S04/S05/S06 节内变量加保序参数形，被 Banach 链全程使用） *)
Variable lbr_minus_pos : forall a b : R, lt a b -> lt zero (minus b a).
Variable lbr_budget : forall x y : X,
  le (gap (step x) (step y)) (mult L (gap x y)).
Variable lbr_gap_nonneg : forall x y : X, le zero (gap x y).
Variable lbr_gap_sym : forall x y : X, Id (gap x y) (gap y x).
Variable lbr_gap_tri : forall x y z : X,
  le (gap x z) (plus (gap x y) (gap y z)).
Variable lbr_gap_zero : forall x y : X, Id (gap x y) zero -> Id x y.
Variable lbr_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (lbr_r_pow L N)) eps).

(* 1−L 严格正（lbr_minus_pos 参数位使用）与 1 = (1−L) + L 代数基石 *)
Let lbr_s_pos : lt zero (minus one L) := lbr_minus_pos L one lbr_L_lt_one.
Let invs := inv_pos (minus one L) lbr_s_pos.

(* 收敛证书（ε-刻画定义形，Set 层；clim_unique 传递与不动点结论用） *)
Definition lbr_clim (u : nat -> X) (l : X) : Set :=
  forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n -> lt (gap (u n) l) eps).

Variable lbr_clim_unique : forall (u : nat -> X) (l1 l2 : X),
  lbr_clim u l1 -> lbr_clim u l2 -> Id l1 l2.

(* 完备性接口参数位（S01 cauchy_complete_S 参数形同形对应） *)
Variable lbr_complete : forall (u : nat -> X),
  (forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n -> lt (gap (u m) (u n)) eps)) ->
  sigT (fun l : X => lbr_clim u l).

(* 不动点（Set 层 Id 面） *)
Definition lbr_fixed_point (x : X) : Set := Id (step x) x.

(* ===== 基础代数件 ===== *)

Lemma lbr_opp_zero : Id (opp zero) zero.
Proof.
  exact (id_trans (id_sym (id_trans (plus_comm zero (opp zero))
                                    (plus_zero (opp zero))))
                  (plus_opp zero)).
Qed.

Lemma lbr_minus_one_L_le_one : le (minus one L) one.
Proof.
  unfold minus.
  apply (le_id_r _ _ _ (plus_zero one)).
  exact (le_plus_compat one one (opp L) zero (le_refl one)
           (le_id_r (opp L) (opp zero) zero lbr_opp_zero
              (opp_le_compat zero L lbr_L_nonneg))).
Qed.

(* g ≤ g/(1−L)：伸缩相消比例常数的吸收（c 非负即可，无需 c > 0） *)
Lemma lbr_le_scaled : forall c : R, le zero c ->
  le c (mult c invs).
Proof.
  intros c Hc.
  assert (Hcs : le (mult c (minus one L)) c).
  { apply (le_trans _ (mult (minus one L) c)).
    - apply (le_id_l (mult c (minus one L)) (mult (minus one L) c)
                     (mult (minus one L) c) (mult_comm c (minus one L))
                     (le_refl _)).
    - apply (le_trans _ (mult one c)).
      + exact (le_mult_compat_weak (minus one L) one c Hc
                  lbr_minus_one_L_le_one).
      + apply (le_id_r _ _ _ (id_trans (mult_comm one c) (mult_one c))).
        apply le_refl. }
  apply (le_trans c (mult (mult c (minus one L)) invs) (mult c invs)).
  - apply (le_id_l c (mult (mult c (minus one L)) invs)
                     (mult (mult c (minus one L)) invs)
             (id_trans (id_sym (mult_one c))
              (id_trans (id_sym (id_cong (fun z => mult c z)
                                  (inv_pos_correct (minus one L) lbr_s_pos)))
                        (mult_assoc c (minus one L) invs)))
             (le_refl _)).
  - exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hcs).
Qed.

(* 半分（S01 half_pos/half_twice 使用）: ∀eps>0 ∃e'>0, e'+e' = eps *)
Lemma lbr_half : forall eps : R, lt zero eps ->
  sigT (fun e' : R => And (lt zero e') (Id (plus e' e') eps)).
Proof.
  intros eps Hep.
  exists (mult (inv_pos (plus one one) two_pos) eps).
  split.
  - exact (half_pos eps Hep).
  - exact (half_twice eps).
Qed.

(* ===== 几何尾和载体与伸缩相消恒等式 ===== *)

Fixpoint lbr_rsum (g : nat -> R) (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S j => plus (lbr_rsum g j) (g j)
  end.

Lemma lbr_rsum_ext : forall (g h : nat -> R) (k : nat),
  (forall i : nat, NatLe i k -> Id (g i) (h i)) ->
  Id (lbr_rsum g k) (lbr_rsum h k).
Proof.
  intros g h k. induction k as [| k IH]; intros Hik.
  - simpl. apply id_refl.
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (g k))
             (IH (fun i Hive => Hik i (NatLe_lift i (Datatypes.S k)
                    (Nat.le_le_succ_r i k (NatLe_drop i k Hive))))))).
    apply (id_trans (id_cong (fun z => plus (lbr_rsum h k) z)
             (Hik k (NatLe_lift k (Datatypes.S k)
                    (Nat.le_le_succ_r k k (Nat.le_refl k)))))).
    apply id_refl.
Qed.

Lemma lbr_rsum_mono : forall (g h : nat -> R) (k : nat),
  (forall i : nat, NatLe i k -> le (g i) (h i)) ->
  le (lbr_rsum g k) (lbr_rsum h k).
Proof.
  intros g h k. induction k as [| k IH]; intros Hik.
  - simpl. apply le_refl.
  - simpl.
    apply (le_plus_compat (lbr_rsum g k) (lbr_rsum h k) (g k) (h k)).
    + apply (IH (fun i Hive => Hik i (NatLe_lift i (Datatypes.S k)
                     (Nat.le_le_succ_r i k (NatLe_drop i k Hive))))).
    + apply (Hik k (NatLe_lift k (Datatypes.S k)
                     (Nat.le_le_succ_r k k (Nat.le_refl k)))).
Qed.

Lemma lbr_rsum_scal : forall (h : nat -> R) (c : R) (k : nat),
  Id (lbr_rsum (fun i => mult c (h i)) k) (mult c (lbr_rsum h k)).
Proof.
  intros h c k. induction k as [| k IH].
  - simpl. exact (id_sym (mult_zero c)).
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult c (h k))) IH)).
    exact (id_sym (distrib c (lbr_rsum h k) (h k))).
Qed.

(* 幂的指数可加性: L^{n+i} = Lⁿ·L^i *)
Lemma lbr_r_pow_add : forall n i : nat,
  Id (lbr_r_pow L (Nat.add n i)) (mult (lbr_r_pow L n) (lbr_r_pow L i)).
Proof.
  intros n i. revert i. induction n as [| n IH]; intro i.
  - exact (id_sym (id_trans (mult_comm one (lbr_r_pow L i))
                            (mult_one (lbr_r_pow L i)))).
  - simpl. exact (id_trans (id_cong (fun z => mult L z) (IH i))
                           (mult_assoc L (lbr_r_pow L n) (lbr_r_pow L i))).
Qed.

(* plus (1−L) L = one（伸缩相消恒等式的代数基石） *)
Lemma lbr_plus_minus_L : Id (plus (minus one L) L) one.
Proof.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc one (opp L) L))
                  (id_trans (id_cong (fun z => plus one z)
                              (id_trans (plus_comm (opp L) L) (plus_opp L)))
                            (plus_zero one))).
Qed.

(* 伸缩步恒等式: (1−L)·(X·c) + (L·X)·c = X·c *)
Lemma lbr_minus_plus_scal : forall Z c : R,
  Id (plus (mult (minus one L) (mult Z c)) (mult (mult L Z) c)) (mult Z c).
Proof.
  intros Z c.
  apply (id_trans (id_cong (fun z => plus z (mult (mult L Z) c))
                            (mult_assoc (minus one L) Z c))).
  apply (id_trans (id_sym (mult_plus_distr_r (mult (minus one L) Z) (mult L Z) c))).
  apply (id_trans (id_cong (fun z => mult z c)
                            (id_sym (mult_plus_distr_r (minus one L) L Z)))).
  apply (id_trans (id_cong (fun z => mult (mult z Z) c) lbr_plus_minus_L)).
  exact (id_trans (id_sym (mult_assoc one Z c))
                  (id_trans (mult_comm one (mult Z c)) (mult_one (mult Z c)))).
Qed.

(* 伸缩相消恒等式: (1−L)·Σ_{i<k} L^i·c + L^k·c = c *)
Lemma lbr_geom_telescope : forall c : R, forall k : nat,
  Id (plus (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
           (mult (lbr_r_pow L k) c))
     c.
Proof.
  intros c k. induction k as [| k IH].
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult one c))
                              (mult_zero (minus one L)))).
    apply (id_trans (id_cong (fun z => plus zero z)
                              (id_trans (mult_comm one c) (mult_one c)))).
    exact (id_trans (plus_comm zero c) (plus_zero c)).
  - simpl.
    apply (id_trans (id_cong (fun z => plus z (mult (mult L (lbr_r_pow L k)) c))
              (distrib (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                       (mult (lbr_r_pow L k) c)))).
    apply (id_trans (id_sym (plus_assoc (mult (minus one L)
                                              (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
                                        (mult (minus one L) (mult (lbr_r_pow L k) c))
                                        (mult (mult L (lbr_r_pow L k)) c)))).
    apply (id_trans (id_cong (fun z => plus (mult (minus one L)
                                                  (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) z)
                              (lbr_minus_plus_scal (lbr_r_pow L k) c))).
    exact IH.
Qed.

(* 几何尾和上界: Σ_{i<k} L^i·c ≤ c/(1−L) *)
Lemma lbr_geom_tail_le : forall c : R, le zero c -> forall k : nat,
  le (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k) (mult c invs).
Proof.
  intros c Hc k.
  assert (Hpow : le zero (mult (lbr_r_pow L k) c)).
  { apply (le_trans _ (mult zero c)).
    - apply (le_id_l zero (mult zero c) (mult zero c)
               (id_sym (id_trans (mult_comm zero c) (mult_zero c)))
               (le_refl (mult zero c))).
    - exact (le_mult_compat_weak zero (lbr_r_pow L k) c Hc
                (lbr_r_pow_nonneg L lbr_L_nonneg k)). }
  assert (Hst : le (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) c).
  { apply (le_id_r _ _ _ (lbr_geom_telescope c k)).
    exact (le_plus_nonneg_r (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k))
                            (mult (lbr_r_pow L k) c) Hpow). }
  apply (le_id_l (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                 (mult (mult (minus one L) (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)) invs)
                 (mult c invs)).
  - exact (id_trans (id_sym (mult_one (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)))
             (id_trans (id_sym (id_cong (fun z => mult (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k) z)
                                 (inv_pos_correct (minus one L) lbr_s_pos)))
                       (id_trans (mult_assoc (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                                                      (minus one L) invs)
                                 (id_cong (fun z => mult z invs)
                                          (mult_comm (lbr_rsum (fun i => mult (lbr_r_pow L i) c) k)
                                                     (minus one L)))))).
  - exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hst).
Qed.

(* ===== 加法消去与 g ≤ L·g ⟹ g ≤ 0（唯一性的代数核） ===== *)

Lemma lbr_le_plus_cancel : forall a b c : R, le (plus a b) (plus c b) -> le a c.
Proof.
  intros a b c H.
  assert (Hm : le zero (minus c a)).
  { apply (le_id_r _ _ _ (id_trans (minus_plus_distr c b a b)
                              (id_trans (id_cong (fun z => plus (minus c a) z)
                                                  (plus_opp b))
                                        (plus_zero (minus c a))))).
    exact (le_minus_nonneg (plus a b) (plus c b) H). }
  apply (le_trans _ (plus zero a)).
  - apply (le_id_l a (plus a zero) (plus zero a) (id_sym (plus_zero a))
             (le_id_l (plus a zero) (plus zero a) (plus zero a)
                      (plus_comm a zero) (le_refl _))).
  - apply (le_id_r _ _ _ (id_trans (plus_comm (minus c a) a) (minus_plus_cancel a c))).
    exact (le_plus_compat zero (minus c a) a a Hm (le_refl a)).
Qed.

Lemma lbr_le_self_mult_zero : forall g : R, le g (mult L g) -> le g zero.
Proof.
  intros g Hgle.
  assert (Hgs : le (mult g (minus one L)) zero).
  { apply (lbr_le_plus_cancel (mult g (minus one L)) (mult g L) zero).
    apply (le_id_l (plus (mult g (minus one L)) (mult g L)) g
                   (plus zero (mult g L))
                   (id_sym (id_trans (id_sym (mult_one g))
                             (id_trans (id_sym (id_cong (fun z => mult g z) lbr_plus_minus_L))
                                       (distrib g (minus one L) L))))
                   (le_trans g (mult g L) (plus zero (mult g L))
                             (le_id_r _ _ _ (mult_comm L g) Hgle)
                             (le_id_l (mult g L) (plus (mult g L) zero)
                                      (plus zero (mult g L))
                                (id_sym (plus_zero (mult g L)))
                                (le_id_l (plus (mult g L) zero)
                                         (plus zero (mult g L))
                                         (plus zero (mult g L))
                                   (plus_comm (mult g L) zero) (le_refl _))))). }
  apply (le_id_l g (mult (mult g (minus one L)) invs) zero
             (id_trans (id_sym (mult_one g))
                       (id_trans (id_sym (id_cong (fun z => mult g z)
                                           (inv_pos_correct (minus one L) lbr_s_pos)))
                                 (mult_assoc g (minus one L) invs)))
             (le_id_r _ _ _ (id_trans (mult_comm zero invs) (mult_zero invs))
                (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos) Hgs))).
Qed.

(* ===== 迭代序列的 Cauchy 模数 ===== *)

(* 比例常数 C := g₀/(1−L) 非负 *)
Lemma lbr_scaled_nonneg : forall x0 : X, le zero (mult (gap (step x0) x0) invs).
Proof.
  intro x0.
  apply (le_trans _ (mult zero invs)).
  - apply (le_id_l zero (mult zero invs) (mult zero invs)
             (id_sym (id_trans (mult_comm zero invs) (mult_zero invs)))
             (le_refl (mult zero invs))).
  - exact (le_mult_compat_weak zero (gap (step x0) x0) invs
              (lt_le_iff zero invs (inl (inv_pos_pos (minus one L) lbr_s_pos)))
              (lbr_gap_nonneg (step x0) x0)).
Qed.

Lemma lbr_gap_le_scaled : forall x0 : X,
  le (gap (step x0) x0) (mult (gap (step x0) x0) invs).
Proof.
  intro x0. exact (lbr_le_scaled (gap (step x0) x0) (lbr_gap_nonneg (step x0) x0)).
Qed.

(* 三角链和: gap(u_n, u_{n+S k}) ≤ Σ_{i≤k} gap(u_{S(n+i)}, u_{n+i}) *)
Lemma lbr_iter_gap_chain : forall (x0 : X) (k n : nat),
  le (gap (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
     (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                     (lbr_iter X step (Nat.add n i) x0))
               (Datatypes.S k)).
Proof.
  intros x0 k n. induction k as [| k IH].
  - assert (E1 : Nat.add n (Datatypes.S O) = Datatypes.S n) by lia.
    rewrite E1.
    simpl.
    assert (E0 : Nat.add n O = n) by lia.
    rewrite E0.
    apply (le_trans _ (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))).
    + apply (le_id_l (gap (lbr_iter X step n x0) (lbr_iter X step (Datatypes.S n) x0))
                     (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                     (lbr_gap_sym (lbr_iter X step n x0) (lbr_iter X step (Datatypes.S n) x0))
                     (le_refl _)).
    + apply (le_trans _ (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)).
      * exact (le_plus_nonneg_r (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero
                  (le_refl zero)).
      * apply (le_id_l (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)
                       (plus zero (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)))
                       (plus zero (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)))
                       (plus_comm (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0)) zero)
                       (le_refl _)).
  - assert (E2 : Nat.add n (Datatypes.S (Datatypes.S k))
                 = Datatypes.S (Nat.add n (Datatypes.S k))) by lia.
    rewrite E2.
    apply (le_trans _ (plus (gap (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                            (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                 (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)))).
    + exact (lbr_gap_tri (lbr_iter X step n x0) (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                         (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)).
    + apply (le_trans _ (plus (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                                        (lbr_iter X step (Nat.add n i) x0))
                                        (Datatypes.S k))
                              (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                   (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)))).
      * exact (le_plus_compat _ _ _ _ IH (le_refl _)).
      * exact (le_plus_compat _ _ _ _ (le_refl (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add n i)) x0)
                                                                  (lbr_iter X step (Nat.add n i) x0))
                                                 (Datatypes.S k)))
                              (le_id_l (gap (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                             (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0))
                                       (gap (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)
                                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                                       (gap (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0)
                                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                                       (lbr_gap_sym (lbr_iter X step (Nat.add n (Datatypes.S k)) x0)
                                                    (lbr_iter X step (Datatypes.S (Nat.add n (Datatypes.S k))) x0))
                                       (le_refl _))).
Qed.

(* 非对角界: gap(u_m, u_{m+S k}) ≤ L^m·C（链和＋几何尾和） *)
Lemma lbr_iter_offdiag_le : forall (x0 : X) (m k : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step (Nat.add m (Datatypes.S k)) x0))
     (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)).
Proof.
  intros x0 m k.
  apply (le_trans _ (lbr_rsum (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add m i)) x0)
                                              (lbr_iter X step (Nat.add m i) x0))
                              (Datatypes.S k)) _).
  - exact (lbr_iter_gap_chain x0 k m).
  - apply (le_trans _ (lbr_rsum (fun i => mult (lbr_r_pow L m)
                                                (mult (lbr_r_pow L i) (gap (step x0) x0)))
                                (Datatypes.S k)) _).
    + exact (le_id_r _ _ _ (lbr_rsum_ext (fun i => mult (lbr_r_pow L (Nat.add m i)) (gap (step x0) x0))
                                (fun i => mult (lbr_r_pow L m) (mult (lbr_r_pow L i) (gap (step x0) x0)))
                                (Datatypes.S k)
                                (fun i _ => id_trans (id_cong (fun z => mult z (gap (step x0) x0))
                                                 (lbr_r_pow_add m i))
                                        (id_sym (mult_assoc (lbr_r_pow L m) (lbr_r_pow L i)
                                                    (gap (step x0) x0)))))
                (lbr_rsum_mono (fun i => gap (lbr_iter X step (Datatypes.S (Nat.add m i)) x0)
                                               (lbr_iter X step (Nat.add m i) x0))
                               (fun i => mult (lbr_r_pow L (Nat.add m i)) (gap (step x0) x0))
                               (Datatypes.S k)
                               (fun i _ => lbr_iter_step_gap_decay X gap step L lbr_L_nonneg
                                             lbr_budget (Nat.add m i) x0))).
    + exact (le_id_l _ _ _ (lbr_rsum_scal (fun i => mult (lbr_r_pow L i) (gap (step x0) x0))
                              (lbr_r_pow L m) (Datatypes.S k))
                (lbr_mult_compat_r (lbr_rsum (fun i => mult (lbr_r_pow L i) (gap (step x0) x0))
                                             (Datatypes.S k))
                                   (mult (gap (step x0) x0) invs)
                                   (lbr_r_pow L m)
                                   (lbr_r_pow_nonneg L lbr_L_nonneg m)
                                   (lbr_geom_tail_le (gap (step x0) x0)
                                      (lbr_gap_nonneg (step x0) x0) (Datatypes.S k)))).
Qed.

(* 对角界: gap(u_m, u_m) ≤ 2·L^m·C（对称＋三角＋衰减） *)
Lemma lbr_iter_diag_le : forall (x0 : X) (m : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step m x0))
     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
           (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
Proof.
  intros x0 m.
  assert (Htail : le (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                     (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
  { apply (le_trans _ (mult (lbr_r_pow L m) (gap (step x0) x0))).
    - exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget m x0).
    - exact (lbr_mult_compat_r (gap (step x0) x0)
                               (mult (gap (step x0) x0) invs)
                               (lbr_r_pow L m)
                               (lbr_r_pow_nonneg L lbr_L_nonneg m)
                               (lbr_gap_le_scaled x0)). }
  apply (le_trans _ (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                          (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))).
  - apply (le_trans _ (plus (gap (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0))
                            (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))).
    + exact (lbr_gap_tri (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)).
    + apply (le_id_l (plus (gap (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (plus (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0))
                           (gap (lbr_iter X step (Datatypes.S m) x0) (lbr_iter X step m x0)))
                     (id_cong (fun z => plus z (gap (lbr_iter X step (Datatypes.S m) x0)
                                                     (lbr_iter X step m x0)))
                              (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step (Datatypes.S m) x0)))
                     (le_refl _)).
  - exact (le_plus_compat _ _ _ _ Htail Htail).
Qed.

(* 主严格模数: arch 常数取 (1−L)+g₀ > 0 吸收 g₀ 可零性——
   ∀eps>0 ∃N ∀n≥N: Lⁿ·(g₀/(1−L)) < eps *)
Lemma lbr_iter_master_lt : forall (x0 : X) (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)) eps).
Proof.
  intros x0 eps Hep.
  assert (Harchpos : lt zero (plus (gap (step x0) x0) (minus one L))).
  { exact (plus_le_lt_pos (gap (step x0) x0) (minus one L)
             (lbr_gap_nonneg (step x0) x0) lbr_s_pos). }
  destruct (lbr_arch (plus (gap (step x0) x0) (minus one L)) Harchpos
                     (mult eps (minus one L))
                     (mult_positive eps (minus one L) Hep lbr_s_pos)) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (mult (lbr_r_pow L N) (gap (step x0) x0)) invs) _).
  - apply (le_id_l (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                   (mult (mult (lbr_r_pow L n) (gap (step x0) x0)) invs)
                   (mult (mult (lbr_r_pow L N) (gap (step x0) x0)) invs)).
    + exact (mult_assoc (lbr_r_pow L n) (gap (step x0) x0) invs).
    + exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)
               (le_mult_compat_weak (lbr_r_pow L n) (lbr_r_pow L N) (gap (step x0) x0)
                  (lbr_gap_nonneg (step x0) x0)
                  (lbr_r_pow_dec L lbr_L_nonneg lbr_L_lt_one N n Hn))).
  - apply (le_lt_trans _ (mult (mult (plus (gap (step x0) x0) (minus one L))
                                        (lbr_r_pow L N)) invs) _).
    + exact (le_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)
               (le_trans (mult (lbr_r_pow L N) (gap (step x0) x0))
                         (mult (gap (step x0) x0) (lbr_r_pow L N))
                         (mult (plus (gap (step x0) x0) (minus one L)) (lbr_r_pow L N))
                 (le_id_l (mult (lbr_r_pow L N) (gap (step x0) x0))
                          (mult (gap (step x0) x0) (lbr_r_pow L N))
                          (mult (gap (step x0) x0) (lbr_r_pow L N))
                          (mult_comm (lbr_r_pow L N) (gap (step x0) x0))
                          (le_refl _))
                 (le_mult_compat_weak (gap (step x0) x0)
                                      (plus (gap (step x0) x0) (minus one L))
                                      (lbr_r_pow L N)
                                      (lbr_r_pow_nonneg L lbr_L_nonneg N)
                                      (le_plus_nonneg_r (gap (step x0) x0) (minus one L)
                                         (lt_le_iff zero (minus one L) (inl lbr_s_pos)))))).
    + apply (lt_id_r _ _ _ (id_trans (id_sym (mult_assoc eps (minus one L) invs))
                                (id_trans (id_cong (fun z => mult eps z)
                                                    (inv_pos_correct (minus one L) lbr_s_pos))
                                          (mult_one eps)))).
      apply (lt_mult_compat _ _ _ (inv_pos_pos (minus one L) lbr_s_pos)).
      exact HN.
Qed.

(* 迭代序列 Cauchy 模数（完备性槽的供给面） *)
Lemma lbr_iter_cauchy : forall x0 : X, forall eps : R, lt zero eps ->
  sigT (fun N : nat => forall m n : nat,
    NatLe N m -> NatLe N n -> lt (gap (lbr_iter X step m x0) (lbr_iter X step n x0)) eps).
Proof.
  intros x0 eps Hep.
  destruct (lbr_half eps Hep) as [e' [He'p He'eq]].
  destruct (lbr_iter_master_lt x0 e' He'p) as [N HN].
  exists N.
  assert (Hinner : forall a b : nat, NatLe N a -> NatLe N b -> NatLe a b ->
            lt (gap (lbr_iter X step a x0) (lbr_iter X step b x0)) eps).
  { intros a b Ha Hb Hab.
    destruct (Nat.eq_dec a b) as [Eab | Hneq].
    - subst b.
      apply (le_lt_trans _ (plus (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs))
                                 (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs))) _).
      + exact (lbr_iter_diag_le x0 a).
      + apply (lt_id_r _ _ _ He'eq).
        apply (lt_plus_compat _ _ _ _ (HN a Ha) (HN a Ha)).
    - assert (Hk : sigT (fun k : nat => Id b (Nat.add a (Datatypes.S k)))).
      { exists (Nat.pred (Nat.sub b a)).
        pose proof (NatLe_drop a b Hab) as Hable.
        apply lbr_eq_id. lia. }
      destruct Hk as [k Hk].
      apply (lt_id_l _ _ _
                (id_cong (fun z => gap (lbr_iter X step a x0) z)
                  (id_cong (fun w => lbr_iter X step w x0) Hk))
                (le_lt_trans _ (mult (lbr_r_pow L a) (mult (gap (step x0) x0) invs)) _
                   (lbr_iter_offdiag_le x0 a k)
                   (lt_le_trans _ _ _ (HN a Ha)
                      (le_id_r _ _ _ He'eq
                         (le_plus_nonneg_r e' e' (lt_le_iff zero e' (inl He'p))))))).
  }
  intros m n Hm Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - apply (Hinner m n Hm Hn).
    exact (NatLe_lift m n (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
  - apply (Nat.leb_gt m n) in Emn.
    apply (lt_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                   (gap (lbr_iter X step n x0) (lbr_iter X step m x0)) eps).
    + exact (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step n x0)).
    + apply (Hinner n m Hn Hm).
      exact (NatLe_lift n m (Nat.lt_le_incl _ _ Emn)).
Qed.

(* ===== Banach 不动点定理与唯一性 ===== *)

Theorem lbr_banach_fixed_point : forall x0 : X,
  sigT (fun l : X => And (lbr_fixed_point l)
                         (lbr_clim (fun n : nat => lbr_iter X step n x0) l)).
Proof.
  intros x0.
  destruct (lbr_complete (fun n : nat => lbr_iter X step n x0) (lbr_iter_cauchy x0)) as [l Hcl].
  exists l. split.
  - unfold lbr_fixed_point.
    apply id_sym.
    apply (lbr_clim_unique (fun n : nat => step (lbr_iter X step n x0)) l (step l)).
    + (* 平移序列 w → l：三角链＋几何衰减＋Hcl *)
      intros eps Hep.
      destruct (lbr_half eps Hep) as [e' [He'p He'eq]].
      destruct (Hcl e' He'p) as [Nc HNc].
      destruct (lbr_iter_master_lt x0 e' He'p) as [Nd HNd].
      exists (Nat.max Nc Nd). intros n Hn.
      assert (Hnc : NatLe Nc n).
      { exact (NatLe_lift Nc n (Nat.le_trans Nc (Nat.max Nc Nd) n (Nat.le_max_l Nc Nd)
                                  (NatLe_drop (Nat.max Nc Nd) n Hn))). }
      assert (Hnd : NatLe Nd n).
      { exact (NatLe_lift Nd n (Nat.le_trans Nd (Nat.max Nc Nd) n (Nat.le_max_r Nc Nd)
                                  (NatLe_drop (Nat.max Nc Nd) n Hn))). }
      apply (le_lt_trans _ (plus (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                                 (gap (lbr_iter X step n x0) l)) _).
      * exact (lbr_gap_tri (step (lbr_iter X step n x0)) (lbr_iter X step n x0) l).
      * apply (lt_id_r _ _ _ He'eq).
        assert (Hd1 : le (gap (lbr_iter X step (Datatypes.S n) x0) (lbr_iter X step n x0))
                         (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
        { apply (le_trans _ (mult (lbr_r_pow L n) (gap (step x0) x0)) _).
          - exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget n x0).
          - exact (lbr_mult_compat_r (gap (step x0) x0)
                                     (mult (gap (step x0) x0) invs)
                                     (lbr_r_pow L n)
                                     (lbr_r_pow_nonneg L lbr_L_nonneg n)
                                     (lbr_gap_le_scaled x0)). }
        apply (lt_plus_compat _ _ _ _
                  (le_lt_trans _ _ _ Hd1 (HNd n Hnd))
                  (HNc n Hnc)).
    + (* 平移序列 w → step l：预算面＋L ≤ 1＋Hcl *)
      intros eps Hep.
      destruct (Hcl eps Hep) as [Nc HNc].
      exists Nc. intros n Hn.
      apply (le_lt_trans _ (gap (lbr_iter X step n x0) l) _).
      * apply (le_id_r _ _ _ (id_trans (mult_comm one (gap (lbr_iter X step n x0) l))
                                  (mult_one (gap (lbr_iter X step n x0) l)))).
        apply (le_trans _ (mult L (gap (lbr_iter X step n x0) l))).
        -- exact (lbr_budget (lbr_iter X step n x0) l).
        -- exact (le_mult_compat_weak L one (gap (lbr_iter X step n x0) l)
                    (lbr_gap_nonneg (lbr_iter X step n x0) l)
                    (lt_le_iff L one (inl lbr_L_lt_one))).
      * exact (HNc n Hn).
  - exact Hcl.
Qed.

(* 收缩不动点的自隙为零（收缩面给出 d(x,x)=0） *)
Lemma lbr_fix_self_gap : forall x : X, lbr_fixed_point x -> Id (gap x x) zero.
Proof.
  intros x Hfix. unfold lbr_fixed_point in Hfix.
  apply (le_antisym (gap x x) zero).
  - apply (lbr_le_self_mult_zero (gap x x)).
    apply (le_id_l (gap x x) (gap (step x) (step x)) (mult L (gap x x))).
    + exact (id_trans (id_cong (fun z => gap z x) (id_sym Hfix))
                      (id_sym (id_cong (fun z => gap (step x) z) Hfix))).
    + exact (lbr_budget x x).
  - exact (lbr_gap_nonneg x x).
Qed.

Theorem lbr_fixed_point_unique : forall l1 l2 : X,
  lbr_fixed_point l1 -> lbr_fixed_point l2 -> Id l1 l2.
Proof.
  intros l1 l2 H1 H2.
  unfold lbr_fixed_point in H1, H2.
  apply (lbr_gap_zero l1 l2).
  apply (le_antisym (gap l1 l2) zero).
  - apply (lbr_le_self_mult_zero (gap l1 l2)).
    (* g ≤ g·0 + (L·g + 0) 换形：外项为不动点自隙（为零），中项为预算面 *)
    assert (Hout1 : Id (gap l1 (step l1)) zero).
    { exact (id_trans (id_cong (fun z => gap l1 z) H1) (lbr_fix_self_gap l1 H1)). }
    assert (Hout2 : Id (gap (step l2) l2) zero).
    { exact (id_trans (id_cong (fun z => gap z l2) H2) (lbr_fix_self_gap l2 H2)). }
    apply (le_trans (gap l1 l2)
                    (plus (gap l1 (step l1))
                          (plus (gap (step l1) (step l2)) (gap (step l2) l2)))
                    (mult L (gap l1 l2))).
    + (* 腿一: 三角两次——gap l1 l2 ≤ g(l1,s1) + (g(s1,s2) + g(s2,l2)) *)
      apply (le_trans _ (plus (gap l1 (step l1)) (gap (step l1) l2))).
      * exact (lbr_gap_tri l1 (step l1) l2).
      * exact (le_plus_compat (gap l1 (step l1)) (gap l1 (step l1))
                              (gap (step l1) l2)
                              (plus (gap (step l1) (step l2)) (gap (step l2) l2))
                              (le_refl (gap l1 (step l1)))
                              (lbr_gap_tri (step l1) (step l2) l2)).
    + (* 肢二: 链和 ≡ 0+(g(s1,s2)+0) ≡ g(s1,s2) ≤ L·g(l1,l2)（预算面闭合） *)
      apply (le_id_l (plus (gap l1 (step l1))
                           (plus (gap (step l1) (step l2)) (gap (step l2) l2)))
                     (plus zero (plus (gap (step l1) (step l2)) zero))
                     (mult L (gap l1 l2))).
      * exact (id_trans (id_cong (fun z => plus z (plus (gap (step l1) (step l2))
                                                        (gap (step l2) l2)))
                                 Hout1)
                        (id_cong (fun w => plus zero (plus (gap (step l1) (step l2)) w))
                                 Hout2)).
      * exact (le_id_l (plus zero (plus (gap (step l1) (step l2)) zero))
                       (gap (step l1) (step l2))
                       (mult L (gap l1 l2))
                       (id_trans (id_cong (fun z => plus zero z)
                                          (plus_zero (gap (step l1) (step l2))))
                                 (id_trans (plus_comm zero (gap (step l1) (step l2)))
                                           (plus_zero (gap (step l1) (step l2)))))
                       (lbr_budget l1 l2)).
  - exact (lbr_gap_nonneg l1 l2).
Qed.

(* ============================================================ *)
(* 后续增量（原断点续写，已闭合语句零改动）:          *)
(*   使用端双件——①对称闭式双向柯西界（无 eps 量词、无 arch 参数位使用，     *)
(*   任意 m n 直取 L^m·C + L^n·C 闭式——柯西模数的易用版）;       *)
(*   ②均匀残差计算器（精度→步数: ∀n≥N 不动点残差                       *)
(*   g(step u_n, u_n) < eps——宿主 attention_iterate_converges 的       *)
(*   数值端姊妹篇，使用桥主件＋master_lt，不动点数值定装闭环）。        *)
(* ============================================================ *)

(* 增量辅件: 比例常数幂乘非负 Lⁿ·C ≥ 0（双向界与残差计算器共用） *)
Lemma lbr_scaled_pow_nonneg : forall (x0 : X) (n : nat),
  le zero (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)).
Proof.
  intros x0 n.
  apply (le_trans _ (mult zero (mult (gap (step x0) x0) invs))).
  - apply (le_id_l zero (mult zero (mult (gap (step x0) x0) invs))
                    (mult zero (mult (gap (step x0) x0) invs))
                    (id_sym (id_trans (mult_comm zero (mult (gap (step x0) x0) invs))
                                      (mult_zero (mult (gap (step x0) x0) invs))))
                    (le_refl (mult zero (mult (gap (step x0) x0) invs)))).
  - exact (le_mult_compat_weak zero (lbr_r_pow L n) (mult (gap (step x0) x0) invs)
              (lbr_scaled_nonneg x0)
              (lbr_r_pow_nonneg L lbr_L_nonneg n)).
Qed.

(* 增量①: 对称闭式双向柯西界——∀m n: g(u_m, u_n) ≤ L^m·C + L^n·C
   （等例=自隙对角界; 序例=离对角界双向对称＋plus 非负吸收; 零 arch 槽） *)
Lemma lbr_iter_cauchy_closed : forall (x0 : X) (m n : nat),
  le (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
Proof.
  intros x0 m n.
  destruct (Nat.eq_dec m n) as [Emn | Hneq].
  - subst n. exact (lbr_iter_diag_le x0 m).
  - destruct (Nat.leb m n) eqn:Eleb.
    + (* m < n: n = m + S k，离对角界＋plus 非负吸收（m 项在前的顺序直接匹配） *)
      assert (Hk : sigT (fun k : nat => Id n (Nat.add m (Datatypes.S k)))).
      { exists (Nat.pred (Nat.sub n m)).
        pose proof (NatLe_lift m n (proj1 (PeanoNat.Nat.leb_le m n) Eleb)) as Hmn.
        pose proof (NatLe_drop m n Hmn) as Hmle.
        apply lbr_eq_id. lia. }
      destruct Hk as [k Hk].
      apply (le_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step m x0)
                          (lbr_iter X step (Nat.add m (Datatypes.S k)) x0))
                     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
      * exact (id_cong (fun z => gap (lbr_iter X step m x0) z)
                       (id_cong (fun w => lbr_iter X step w x0) Hk)).
      * apply (le_trans _ (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))).
        -- exact (lbr_iter_offdiag_le x0 m k).
        -- exact (le_plus_nonneg_r (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                   (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                   (lbr_scaled_pow_nonneg x0 n)).
    + (* n < m 对称: m = n + S k，离对角界取 n 项＋plus 交换律归位 *)
      apply (le_id_l (gap (lbr_iter X step m x0) (lbr_iter X step n x0))
                     (gap (lbr_iter X step n x0) (lbr_iter X step m x0))
                     (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                           (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
      * exact (lbr_gap_sym (lbr_iter X step m x0) (lbr_iter X step n x0)).
      * assert (Hk : sigT (fun k : nat => Id m (Nat.add n (Datatypes.S k)))).
        { exists (Nat.pred (Nat.sub m n)).
          pose proof (proj1 (Nat.leb_gt m n) Eleb) as Hgt.
          apply lbr_eq_id. lia. }
        destruct Hk as [k Hk].
        apply (le_id_l (gap (lbr_iter X step n x0) (lbr_iter X step m x0))
                       (gap (lbr_iter X step n x0)
                            (lbr_iter X step (Nat.add n (Datatypes.S k)) x0))
                       (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                             (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))).
        -- exact (id_cong (fun z => gap (lbr_iter X step n x0) z)
                          (id_cong (fun w => lbr_iter X step w x0) Hk)).
        -- apply (le_trans _ (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))).
           ++ exact (lbr_iter_offdiag_le x0 n k).
           ++ apply (le_trans _ (plus (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))).
              ** exact (le_plus_nonneg_r (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                         (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                         (lbr_scaled_pow_nonneg x0 m)).
              ** exact (le_id_l (plus (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))
                                (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))
                                (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                      (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)))
                                (plus_comm (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))
                                           (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs)))
                                (le_refl (plus (mult (lbr_r_pow L m) (mult (gap (step x0) x0) invs))
                                               (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs))))).
Qed.

(* 增量②: 均匀残差计算器——∀eps>0 ∃N ∀n≥N: g(step u_n, u_n) < eps
   （不动点残差数值定装: 衰减界 ≤ Lⁿ·g₀ ≤ Lⁿ·C < eps 三段换轨；
     知 l 与否两用——无需 Banach 点即可定装精度） *)
Theorem lbr_residual_calc : forall (x0 : X) (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    lt (gap (step (lbr_iter X step n x0)) (lbr_iter X step n x0)) eps).
Proof.
  intros x0 eps Hep.
  destruct (lbr_iter_master_lt x0 eps Hep) as [N HN].
  exists N. intros n Hn.
  apply (le_lt_trans _ (mult (lbr_r_pow L n) (mult (gap (step x0) x0) invs)) _).
  - apply (le_trans _ (mult (lbr_r_pow L n) (gap (step x0) x0))).
    + exact (lbr_iter_step_gap_decay X gap step L lbr_L_nonneg lbr_budget n x0).
    + exact (lbr_mult_compat_r (gap (step x0) x0)
                               (mult (gap (step x0) x0) invs)
                               (lbr_r_pow L n)
                               (lbr_r_pow_nonneg L lbr_L_nonneg n)
                               (lbr_gap_le_scaled x0)).
  - exact (HN n Hn).
Qed.

End LbrBanach.

(* ============================================================ *)
(* 尾取证块: Print Assumptions（零公理判据 Closed）＋烟测双发＋          *)
(*   Separate Extraction 三 Fixpoint（真 let rec 铁证）。               *)
(* ============================================================ *)

Print Assumptions lbr_iter_lipschitz.
Print Assumptions lbr_step_count.
Print Assumptions lbr_r_pow_dec.
Print Assumptions lbr_r_pow_nonneg.
Print Assumptions lbr_r_pow_step_dec.
Print Assumptions lbr_iter_plus.
Print Assumptions lbr_iter_step_gap_decay.
Print Assumptions lbr_affine_diff.
Print Assumptions lbr_affine_budget_proj.
Print Assumptions lbr_affine_iter_contraction.
Print Assumptions lbr_geom_telescope.
Print Assumptions lbr_iter_master_lt.
Print Assumptions lbr_iter_cauchy.
Print Assumptions lbr_banach_fixed_point.
Print Assumptions lbr_fixed_point_unique.
Print Assumptions lbr_iter_cauchy_closed.
Print Assumptions lbr_residual_calc.

(* 烟测双发（数值定装）: lbr_iter 以 nat 实例化——步进函数自复合读数 *)
(* 一发: step := S，五步迭代 0 → 5（迭代 Fixpoint 数值面） *)
Eval vm_compute in (lbr_iter nat Datatypes.S 5 0).
(* 二发: step := 倍加，四步迭代 1 → 16（几何面数值面） *)
Eval vm_compute in (lbr_iter nat (fun k => k * 2) 4 1).

Separate Extraction lbr_iter lbr_r_pow lbr_rsum.
