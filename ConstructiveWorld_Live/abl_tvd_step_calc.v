(* ==========================================================================
   abl_tvd_step_calc.v — UpTVDoeblin tvd 收缩面的步数计算器件（tvc_ 前缀）
   模块名: abl_tvd_step_calc
   数学使命: 把 UpTVDoeblin.v 双点全变差收缩面（tv_doeblin_iter 显式率
     (tv_omd delta) 的 n 次幂、实例面 tvd_dstar_iter_contraction 显式率
     (1 − e^{−2γ/T}) 的 n 次幂）的纯率性陈述升级为「精度→步数」可提取步数
     见证：nat 定点档真 Fixpoint 计算器（严格档首破停机＋燃料充足性见证）＋
     实面 sigT 混合时间模量＋正确性件（接口面与 delta-star 实例面双层）＋
     有理数据实面桥（零 arch 依赖）。
   依赖清单: S01_BaseRing 至 S04_RealExpLogConv（NatLe/Id/real_lt/real_le/
     real_eq/le_mult_compat 系在役）；S07/S08/S09/S12（real_exp_neg_decr/
     real_of_nat/tvd_lt_le 系经 UpTVDoeblin 传递在役）；UpReqIterGeomRate 加
     UpReqMixingTime（mix_omd_lt_one）；UpTVDoeblin（tv_doeblin_iter/
     tvd_dstar_iter_contraction 闭包，Import 使用）；Stdlib QArith.Qring/
     ZArith/Arith/Lia。Require-only，宿主零改动。
   对标行: MixingTimeG2.v mtg_k_calc（Defined 计算器加正确性件，G3 复活面）
     与 UpReqConcMixSel cmk_attention_mixing_time 同族 K9 位；nat 定点档沿
     abl_dyn_step_calc（le 档首件）、abl_attn_step_calc（严格档 ltb 首破）、
     abl_concmix_step_calc（燃料充足性见证）三代模板滚转合并。
   构造性注记: 纯构造性、零公理；语句面全 Set 承载——存在一律 sigT、nat 序
     界一律 NatLe/NatLt（S01:88 Id-of-leb 承载，本件按同型补 NatLt）、合取一
     律 And（S01:46 prod 承载）、实比较一律 real_lt/real_le/real_eq；零 Prop
     连词与 Prop 存在承载、零否定记号书写；非平凡（tvc_k_enum/tvc_pow_iter
     为真 Fixpoint）；可提取（尾 Separate Extraction 验证）。
   编译配方: source Live/toolchain/env.sh 且 unset COQLIB ROCQLIB 且
     ulimit -s 65532 且 nice -19 rocq c -native-compiler no
     -Q vo_local_world_unified_0930 "" abl_tvd_step_calc.v（池内执行）。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S12_B5RecycleSF.
Require Import UpReqIterGeomRate.
Require Import UpReqMixingTime.
Require Import UpTVDoeblin.

Local Open Scope Q_scope.

(* ################ Part 0：Set 层 nat 序界承载（NatLt 补件与 Id 桥） ###### *)

(* S01:88 NatLe（Id-of-leb）的严格对偶：NatLt := Id-of-ltb（同型承载） *)
Definition tvc_NatLt (n m : nat) : Set := Id (Nat.ltb n m) true.

(* Id 到原生 eq 的桥（证明体内换轨用；Set 归纳消入 Prop 合法） *)
Definition tvc_id_eq {A : Set} (x y : A) (H : Id x y) : x = y :=
  match H in Id _ z return (x = z) with id_refl => eq_refl end.

Lemma tvc_NatLt_drop : forall n m : nat, tvc_NatLt n m -> (n < m)%nat.
Proof.
  intros n m H. unfold tvc_NatLt in H.
  destruct (Nat.ltb n m) eqn:E.
  - exact (proj1 (Nat.ltb_lt n m) E).
  - inversion H.
Qed.

Lemma tvc_NatLt_lift : forall n m : nat, (n < m)%nat -> tvc_NatLt n m.
Proof.
  intros n m H. unfold tvc_NatLt.
  destruct (Nat.ltb n m) eqn:E.
  - apply id_refl.
  - exfalso. apply (proj1 (Nat.ltb_ge n m)) in E. lia.
Qed.

(* ################ Part 2：nat 定点档计算器（真 Fixpoint/严格档） ########## *)
(*   模量方程 log(a·kappa 的 N 次幂) < log eps 的 nat 面：kappa = p/q、      *)
(*   初值 a = A、预算 eps = E 的公共尺度定点表示，枚举首次跌破（x < E 严格   *)
(*   停机）的步数 N；上取整衰减步保上界方向。含燃料充足性见证（half 域与     *)
(*   qbound 域两实例）——调用侧可达性承载由 tvc_reach 系自动供给。            *)
(* ######################################################################## *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition tvc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma tvc_ceil_div_le : forall a q : nat,
  NatLe 1 q -> NatLe a (tvc_ceil_div a q * q).
Proof.
  intros a q Hq. apply NatLe_lift.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold tvc_ceil_div.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q
                (proj2 (Nat.neq_0_lt_0 q) Hq')) as Hmb.
  lia.
Qed.

(* 衰减步：x 走 kappa = p/q 的定点乘步（上取整） *)
Definition tvc_iter (p q x : nat) : nat := tvc_ceil_div (x * p) q.

Lemma tvc_iter_step_bound : forall p q x : nat,
  NatLe 1 q -> NatLe (x * p) (tvc_iter p q x * q).
Proof.
  intros p q x Hq. unfold tvc_iter. apply (tvc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：tvc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint tvc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => tvc_iter p q (tvc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma tvc_pow_iter_comm : forall p q x k : nat,
  Id (tvc_pow_iter p q (tvc_iter p q x) k)
     (tvc_iter p q (tvc_pow_iter p q x k)).
Proof.
  intros p q x k. induction k as [| k IH].
  - apply id_refl.
  - simpl. apply (id_cong (tvc_iter p q) IH).
Qed.

(* 枚举器：有界燃料 Fixpoint——x < e 即停（严格档首破停机），否则走衰减步再搜 *)
Fixpoint tvc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (tvc_k_enum f p q (tvc_iter p q x) e)
  end.

(* 可达性承载（全 Set）：存在 k ≤ fuel 使第 k 步上取整值 < e *)
Definition tvc_reach (fuel p q x e : nat) : Set :=
  sigT (fun k : nat => And (NatLe k fuel) (tvc_NatLt (tvc_pow_iter p q x k) e)).

(* 正确性（严格面）：燃料内可达则枚举返回的 N 步处上取整值 < e *)
Theorem tvc_k_enum_strict_correct : forall fuel p q x e : nat,
  tvc_reach fuel p q x e ->
  tvc_NatLt (tvc_pow_iter p q x (tvc_k_enum fuel p q x e)) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hreach.
  - destruct Hreach as [k [Hk Hbound]].
    pose proof (NatLe_drop k 0%nat Hk) as Hk'.
    assert (Hk0 : k = 0%nat) by lia. rewrite Hk0 in Hbound.
    exact Hbound.
  - destruct Hreach as [k [Hk Hbound]].
    change (tvc_k_enum (Datatypes.S f) p q x e)
      with (if Nat.ltb x e then 0%nat else Datatypes.S (tvc_k_enum f p q (tvc_iter p q x) e)).
    destruct (Nat.ltb x e) eqn:Hlt.
    + apply tvc_NatLt_lift. exact (proj1 (Nat.ltb_lt x e) Hlt).
    + pose proof (proj1 (Nat.ltb_ge x e) Hlt) as Hge.
      destruct k as [| k'].
      * exfalso.
        pose proof (tvc_NatLt_drop _ _ Hbound) as Hb0.
        change (tvc_pow_iter p q x 0%nat) with x in Hb0.
        lia.
      * pose proof (tvc_NatLt_drop _ _ Hbound) as HbP.
        change (tvc_iter p q (tvc_pow_iter p q x k') < e)%nat in HbP.
        rewrite <- (tvc_id_eq _ _ (tvc_pow_iter_comm p q x k')) in HbP.
        pose proof (NatLe_drop (Datatypes.S k') (Datatypes.S f) Hk) as Hk'.
        assert (Hk'f : (k' <= f)%nat) by lia.
        assert (Hex' : tvc_reach f p q (tvc_iter p q x) e).
        { refine (existT _ k' _). split.
          - apply NatLe_lift. exact Hk'f.
          - apply tvc_NatLt_lift. exact HbP. }
        specialize (IH p q (tvc_iter p q x) e Hex').
        pose proof (tvc_NatLt_drop _ _ IH) as IHP.
        rewrite (tvc_id_eq _ _ (tvc_pow_iter_comm p q x
                     (tvc_k_enum f p q (tvc_iter p q x) e))) in IHP.
        apply tvc_NatLt_lift. exact IHP.
Qed.

(* 不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma tvc_pow_iter_exact_ge : forall p q x k : nat,
  NatLe 1 p -> NatLe 1 q ->
  NatLe (x * p ^ k) (tvc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply NatLe_lift.
    change (p ^ 0%nat)%nat with 1%nat.
    change (q ^ 0%nat)%nat with 1%nat.
    change (tvc_pow_iter p q x 0%nat) with x.
    rewrite Nat.mul_1_r. apply Nat.le_refl.
  - pose proof (NatLe_drop 1 q Hq) as Hq'.
    pose proof (tvc_iter_step_bound p q (tvc_pow_iter p q x k) Hq) as Hstep.
    pose proof (NatLe_drop (tvc_pow_iter p q x k * p)
                  (tvc_iter p q (tvc_pow_iter p q x k) * q) Hstep) as Hstep'.
    pose proof (NatLe_drop (x * p ^ k) (tvc_pow_iter p q x k * q ^ k) IH) as IH'.
    apply NatLe_lift.
    change (tvc_pow_iter p q x (Datatypes.S k))
      with (tvc_iter p q (tvc_pow_iter p q x k)).
    change (p ^ Datatypes.S k)%nat with (p * p ^ k)%nat.
    change (q ^ Datatypes.S k)%nat with (q * q ^ k)%nat.
    apply (Nat.le_trans _ (tvc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + rewrite <- (Nat.mul_assoc (tvc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (tvc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (tvc_iter p q (tvc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (tvc_iter p q (tvc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* q 的 k 次幂正性（nat 面） *)
Lemma tvc_pow_pos : forall q k : nat, NatLe 1 q -> tvc_NatLt 0 (q ^ k).
Proof.
  intros q k Hq. apply tvc_NatLt_lift.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  induction k as [| k IH].
  - change (q ^ 0%nat)%nat with 1%nat. lia.
  - change (q ^ Datatypes.S k)%nat with (q * q ^ k)%nat.
    assert (H1q : (1 <= q)%nat) by lia.
    assert (H1k : (1 <= q ^ k)%nat) by lia.
    pose proof (Nat.mul_le_mono _ _ _ _ H1q H1k) as Hm. simpl in Hm. lia.
Qed.

(* 模量方程的严格 nat 形：枚举终止则 x·p^N < e·q^N（log 单调下等价面） *)
Theorem tvc_k_enum_ltface : forall fuel p q x e : nat,
  NatLe 1 p -> NatLe 1 q ->
  tvc_reach fuel p q x e ->
  tvc_NatLt (x * p ^ tvc_k_enum fuel p q x e)
            (e * q ^ tvc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (tvc_k_enum_strict_correct fuel p q x e Hterm) as H1.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (tvc_pow_iter_exact_ge p q x (tvc_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H2) as H2'.
  pose proof (tvc_NatLt_drop _ _ (tvc_pow_pos q (tvc_k_enum fuel p q x e) Hq)) as HqN.
  apply tvc_NatLt_lift.
  apply (Nat.le_lt_trans _
           (tvc_pow_iter p q x (tvc_k_enum fuel p q x e)
              * q ^ tvc_k_enum fuel p q x e)).
  - exact H2'.
  - exact (proj1 (Nat.mul_lt_mono_pos_r (q ^ tvc_k_enum fuel p q x e)
                   (tvc_pow_iter p q x (tvc_k_enum fuel p q x e)) e HqN) H1').
Qed.

(* ---------- 严格衰减与燃料充足性 ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据） *)
Lemma tvc_iter_lt_decay : forall p q x : nat,
  NatLe 1 q -> NatLe (x * p + q) (x * q) -> tvc_NatLt (tvc_iter p q x) x.
Proof.
  intros p q x Hq Hdecay. apply tvc_NatLt_lift. unfold tvc_iter, tvc_ceil_div.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hd'.
  destruct (Nat.lt_ge_cases (Nat.div (x * p + q - 1) q) x) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
    assert (Hmon : (x * q <= Nat.div (x * p + q - 1) q * q)%nat)
      by (apply Nat.mul_le_mono_r; exact Hge).
    pose proof (Nat.div_mod_eq (x * p + q - 1) q) as Hdm.
    pose proof (Nat.mod_upper_bound (x * p + q - 1) q
                  (proj2 (Nat.neq_0_lt_0 q) Hq')) as Hmb.
    lia.
Qed.

(* half 域衰减：2·p ≤ q 且 x ≥ 2 时走步严格递降（x·(q−p) ≥ 2(q−p) ≥ q） *)
Lemma tvc_iter_lt_half : forall p q x : nat,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x -> tvc_NatLt (tvc_iter p q x) x.
Proof.
  intros p q x Hp H2p Hx. apply (tvc_iter_lt_decay p q x).
  - apply NatLe_lift.
    pose proof (NatLe_drop 1 p Hp) as Hp'.
    pose proof (NatLe_drop (2 * p) q H2p) as H2p'. lia.
  - apply NatLe_lift.
    pose proof (NatLe_drop 1 p Hp) as Hp'.
    pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
    pose proof (NatLe_drop 2 x Hx) as Hx'.
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma tvc_iter_lt_q : forall p q x : nat,
  NatLe 1 p -> tvc_NatLt p q -> NatLe q x -> tvc_NatLt (tvc_iter p q x) x.
Proof.
  intros p q x Hp Hpq Hx. apply (tvc_iter_lt_decay p q x).
  - apply NatLe_lift.
    pose proof (NatLe_drop 1 p Hp) as Hp'.
    pose proof (tvc_NatLt_drop p q Hpq) as Hpq'. lia.
  - apply NatLe_lift.
    pose proof (NatLe_drop 1 p Hp) as Hp'.
    pose proof (tvc_NatLt_drop p q Hpq) as Hpq'.
    pose proof (NatLe_drop q x Hx) as Hx'.
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H1 : (1 <= q - p)%nat) by lia.
    assert (H2le : (q * 1 <= x * (q - p))%nat) by (apply Nat.mul_le_mono; lia).
    rewrite Nat.mul_1_r in H2le.
    rewrite Hsplit. lia.
Qed.

(* 可达性供给（泛形）：凡预算以上（含预算处）走步严格递降，则 x 步燃料必达 *)
Lemma tvc_reach_gen : forall fuel p q x E : nat,
  tvc_NatLt 0 E -> NatLe x fuel ->
  (forall y : nat, NatLe E y -> tvc_NatLt (tvc_iter p q y) y) ->
  tvc_reach fuel p q x E.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x E HE Hx Hdecay.
  - pose proof (NatLe_drop x 0%nat Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. rewrite Hx0.
    refine (existT _ 0%nat _). split.
    + apply NatLe_lift. lia.
    + exact HE.
  - destruct (Nat.ltb x E) eqn:Hlt.
    + refine (existT _ 0%nat _). split.
      * apply NatLe_lift. lia.
      * simpl. apply tvc_NatLt_lift. exact (proj1 (Nat.ltb_lt x E) Hlt).
    + pose proof (proj1 (Nat.ltb_ge x E) Hlt) as Hge.
      pose proof (Hdecay x (NatLe_lift E x Hge)) as Hdec.
      pose proof (tvc_NatLt_drop _ _ Hdec) as Hdec'.
      assert (Hiterf : (tvc_iter p q x <= f)%nat)
        by (pose proof (NatLe_drop x (Datatypes.S f) Hx); lia).
      destruct (IH p q (tvc_iter p q x) E HE (NatLe_lift _ _ Hiterf) Hdecay)
        as [k [Hk Hb]].
      refine (existT _ (Datatypes.S k) _). split.
      * apply NatLe_lift.
        pose proof (NatLe_drop (Datatypes.S k) (Datatypes.S f) Hk). lia.
      * rewrite (tvc_id_eq _ _ (tvc_pow_iter_comm p q x k)) in Hb. exact Hb.
Qed.

(* 燃料充足性（le 形，CA 系接口沿承）：可达承载的 ≤ 形读出 *)
Theorem tvc_fuel_sufficient_gen : forall fuel p q x E : nat,
  tvc_NatLt 0 E -> NatLe x fuel ->
  (forall y : nat, NatLe E y -> tvc_NatLt (tvc_iter p q y) y) ->
  sigT (fun k : nat => And (NatLe k fuel) (NatLe (tvc_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E HE Hx Hdecay.
  destruct (tvc_reach_gen fuel p q x E HE Hx Hdecay) as [k [Hk Hb]].
  refine (existT _ k _). split.
  - exact Hk.
  - apply NatLe_lift. pose proof (tvc_NatLt_drop _ _ Hb). lia.
Qed.

(* half 域可达性：2·p ≤ q、预算 E ≥ 2，fuel := x 即足（E = 1 处定点档可停滞） *)
Lemma tvc_reach_half : forall fuel p q x E : nat,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  tvc_reach fuel p q x E.
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (tvc_reach_gen fuel p q x E).
  - apply tvc_NatLt_lift. pose proof (NatLe_drop 2 E HE). lia.
  - exact Hx.
  - intros y Hy. apply (tvc_iter_lt_half p q y Hp H2p).
    pose proof (NatLe_drop 2 E HE) as HE2.
    pose proof (NatLe_drop E y Hy). apply NatLe_lift. lia.
Qed.

(* qbound 域可达性：p < q、预算 E ≥ q，fuel := x 即足 *)
Lemma tvc_reach_qbound : forall fuel p q x E : nat,
  NatLe 1 p -> tvc_NatLt p q -> NatLe q E -> NatLe x fuel ->
  tvc_reach fuel p q x E.
Proof.
  intros fuel p q x E Hp Hpq HE Hx.
  apply (tvc_reach_gen fuel p q x E).
  - apply tvc_NatLt_lift.
    pose proof (NatLe_drop q E HE) as HE'.
    pose proof (tvc_NatLt_drop p q Hpq) as Hpq'.
    pose proof (NatLe_drop 1 p Hp) as Hp'. lia.
  - exact Hx.
  - intros y Hy. apply (tvc_iter_lt_q p q y Hp Hpq).
    pose proof (NatLe_drop E y Hy) as Hy'.
    pose proof (NatLe_drop q E HE) as HE'.
    apply NatLe_lift. lia.
Qed.

(* 调用侧自动燃料（half 域）：枚举器读数即严格正确步数 *)
Theorem tvc_k_enum_auto_half : forall p q A E : nat,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> tvc_NatLt E A ->
  tvc_NatLt (tvc_pow_iter p q A (tvc_k_enum A p q A E)) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (tvc_k_enum_strict_correct A p q A E).
  apply (tvc_reach_half A p q A E Hp H2p HE).
  apply NatLe_lift. lia.
Qed.

(* 调用侧自动燃料（qbound 域）：枚举器读数即严格正确步数 *)
Theorem tvc_k_enum_auto_qbound : forall p q A E : nat,
  NatLe 1 p -> tvc_NatLt p q -> NatLe q E -> tvc_NatLt E A ->
  tvc_NatLt (tvc_pow_iter p q A (tvc_k_enum A p q A E)) E.
Proof.
  intros p q A E Hp Hpq HE HAE.
  apply (tvc_k_enum_strict_correct A p q A E).
  apply (tvc_reach_qbound A p q A E Hp Hpq HE).
  apply NatLe_lift. lia.
Qed.

(* 定点档烟测（BB 数值定装）：kappa = 7/10、A = 1000、E = 10 严格档首破 *)
Eval vm_compute in (tvc_k_enum 50 7 10 1000 10).
(* 烟测二：kappa = 1/2（half 域、E ≥ 2）、A = 1000、E = 5 *)
Eval vm_compute in (tvc_k_enum 30 1 2 1000 5).
(* 烟测三：kappa = 3/4（qbound 域、E ≥ q）、A = 50、E = 4 *)
Eval vm_compute in (tvc_k_enum 30 3 4 50 4).

(* ################ tv_rpow 通用幂定律（Part 1/1b/3 公共件） ################ *)

(* tv_rpow 正性：0 < c 则 0 < c 的 n 次幂 *)
Lemma tvc_rpow_pos : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_lt real_zero (tv_rpow c n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [tv_rpow]. exact (real_mult_positive c (tv_rpow c m) Hc IH).
Qed.

(* tv_rpow 不超过 1：0 < c ≤ 1 则 c 的 n 次幂 ≤ 1 *)
Lemma tvc_rpow_le_one : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (n : nat),
  real_le (tv_rpow c n) real_one.
Proof.
  intros c Hc0 Hc1 n. induction n as [| m IH].
  - apply real_le_refl.
  - cbn [tv_rpow].
    apply (real_le_trans (real_mult c (tv_rpow c m))
             (real_mult real_one (tv_rpow c m)) real_one).
    + exact (real_le_mult_compat c real_one (tv_rpow c m)
               (tvc_rpow_pos c Hc0 m) Hc1).
    + apply (real_le_trans (real_mult real_one (tv_rpow c m))
               (tv_rpow c m) real_one).
      * apply (RealSetoid.real_eq_le).
        exact (real_eq_trans (real_mult real_one (tv_rpow c m))
                 (real_mult (tv_rpow c m) real_one) (tv_rpow c m)
                 (real_mult_comm real_one (tv_rpow c m))
                 (real_mult_one (tv_rpow c m))).
      * exact IH.
Qed.

(* tv_rpow 指数反单调：m ≤ n 则 c 的 n 次幂 ≤ c 的 m 次幂 *)
Lemma tvc_rpow_dec_iter : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (m n : nat),
  NatLe m n -> real_le (tv_rpow c n) (tv_rpow c m).
Proof.
  intros c Hc0 Hc1 m. induction m as [| m' IH]; intros n Hle.
  - apply (tvc_rpow_le_one c Hc0 Hc1 n).
  - destruct n as [| n'].
    + exfalso. pose proof (NatLe_drop (Datatypes.S m') 0%nat Hle) as Hc. lia.
    + pose proof (NatLe_drop (Datatypes.S m') (Datatypes.S n') Hle) as Hle'.
      assert (Hmn : (m' <= n')%nat) by lia.
      apply (RealSetoid.real_le_id_l (tv_rpow c (Datatypes.S n'))
               (real_mult c (tv_rpow c n')) (real_mult c (tv_rpow c m'))).
      * apply real_eq_refl.
      * exact (tvd_le_mult_compat_l c (tv_rpow c n') (tv_rpow c m')
                  Hc0 (IH n' (NatLe_lift _ _ Hmn))).
Qed.

(* tv_rpow 对 real_eq 的函子性（换底直连用） *)
Lemma tvc_rpow_wd : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (tv_rpow x n) (tv_rpow y n).
Proof.
  intros x y n H. induction n as [| n IH].
  - apply real_eq_refl.
  - cbn [tv_rpow].
    exact (RealSetoid.real_eq_mult_compat x (tv_rpow x n) y (tv_rpow y n) H IH).
Qed.

(* ################ Part 3：实面桥（有理数据 kappa = p/q，零 arch 依赖） #### *)

(* real_one / real_zero 的 Q 投影桥与 real_of_nat 逐点投影件：本件实面桥
   全走 real_eq 项链（tvc_of_nat_plus/mult + tvc_mult_plus_distr_r），
   零 Q 投影使用，故不设 Q 投影件。 *)

(* 乘法对加法的右分配（逐点环面） *)
Lemma tvc_mult_plus_distr_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z)
          (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. apply real_eq_of_zero_diff. intro k.
  rewrite (real_mult_proj (real_plus x y) z k).
  rewrite (real_plus_proj x y k).
  rewrite (real_plus_proj (real_mult x z) (real_mult y z) k).
  rewrite (real_mult_proj x z k).
  rewrite (real_mult_proj y z k).
  ring.
Qed.

(* real_of_nat 加法同态 *)
Lemma tvc_of_nat_plus : forall a b : nat,
  real_eq (real_of_nat (a + b)) (real_plus (real_of_nat a) (real_of_nat b)).
Proof.
  intros a b. induction a as [| a IH].
  - exact (real_eq_sym (real_plus real_zero (real_of_nat b)) (real_of_nat b)
             (tvd_plus_zero_l (real_of_nat b))).
  - change (real_of_nat (Datatypes.S a + b))
      with (real_plus real_one (real_of_nat (a + b))).
    change (real_of_nat (Datatypes.S a))
      with (real_plus real_one (real_of_nat a)).
    apply (real_eq_trans
             (real_plus real_one (real_of_nat (a + b)))
             (real_plus real_one (real_plus (real_of_nat a) (real_of_nat b)))).
    + exact (RealSetoid.real_eq_plus_compat real_one (real_of_nat (a + b))
               real_one (real_plus (real_of_nat a) (real_of_nat b))
               (real_eq_refl real_one) IH).
    + exact (real_plus_assoc real_one (real_of_nat a) (real_of_nat b)).
Qed.

(* real_of_nat 乘法同态 *)
Lemma tvc_of_nat_mult : forall a b : nat,
  real_eq (real_of_nat (a * b)) (real_mult (real_of_nat a) (real_of_nat b)).
Proof.
  intros a b. induction a as [| a IH].
  - exact (real_eq_sym (real_mult real_zero (real_of_nat b)) real_zero
             (real_eq_trans (real_mult real_zero (real_of_nat b))
                (real_mult (real_of_nat b) real_zero) real_zero
                (real_mult_comm real_zero (real_of_nat b))
                (real_mult_zero (real_of_nat b)))).
  - change (real_of_nat (Datatypes.S a * b))
      with (real_of_nat (b + a * b)).
    apply (real_eq_trans (real_of_nat (b + a * b))
             (real_plus (real_of_nat b) (real_of_nat (a * b)))).
    + exact (tvc_of_nat_plus b (a * b)).
    + exact (real_eq_sym
               (real_mult (real_of_nat (Datatypes.S a)) (real_of_nat b))
               (real_plus (real_of_nat b) (real_of_nat (a * b)))
               (real_eq_trans
                  (real_mult (real_plus real_one (real_of_nat a))
                             (real_of_nat b))
                  (real_plus (real_mult real_one (real_of_nat b))
                             (real_mult (real_of_nat a) (real_of_nat b)))
                  (real_plus (real_of_nat b) (real_of_nat (a * b)))
                  (tvc_mult_plus_distr_r real_one (real_of_nat a)
                     (real_of_nat b))
                  (RealSetoid.real_eq_plus_compat
                     (real_mult real_one (real_of_nat b))
                     (real_mult (real_of_nat a) (real_of_nat b))
                     (real_of_nat b)
                     (real_of_nat (a * b))
                     (real_eq_trans (real_mult real_one (real_of_nat b))
                        (real_mult (real_of_nat b) real_one) (real_of_nat b)
                        (real_mult_comm real_one (real_of_nat b))
                        (real_mult_one (real_of_nat b)))
                     (real_eq_sym _ _ IH)))).
Qed.

(* 左单位律 *)
Lemma tvc_mult_one_l : forall t : Real, real_eq (real_mult real_one t) t.
Proof.
  intro t.
  exact (real_eq_trans (real_mult real_one t) (real_mult t real_one) t
           (real_mult_comm real_one t) (real_mult_one t)).
Qed.

(* 逆元唯一性：y·z == 1 则 z == inv y *)
Lemma tvc_inv_unique : forall (y z : Real) (Hy : real_lt real_zero y),
  real_eq (real_mult y z) real_one -> real_eq z (real_inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  apply (real_eq_trans z
           (real_mult z (real_mult y (real_inv_pos y Hy)))).
  - exact (real_eq_trans z (real_mult z real_one)
             (real_mult z (real_mult y (real_inv_pos y Hy)))
             (real_eq_sym (real_mult z real_one) z (real_mult_one z))
             (RealSetoid.real_eq_mult_compat z real_one
                z (real_mult y (real_inv_pos y Hy))
                (real_eq_refl z)
                (real_eq_sym (real_mult y (real_inv_pos y Hy)) real_one
                   (real_inv_pos_correct y Hy)))).
  - apply (real_eq_trans
             (real_mult z (real_mult y (real_inv_pos y Hy)))
             (real_mult real_one (real_inv_pos y Hy))).
    + exact (real_eq_trans
               (real_mult z (real_mult y (real_inv_pos y Hy)))
               (real_mult (real_mult y z) (real_inv_pos y Hy))
               (real_mult real_one (real_inv_pos y Hy))
               (real_eq_trans
                  (real_mult z (real_mult y (real_inv_pos y Hy)))
                  (real_mult (real_mult z y) (real_inv_pos y Hy))
                  (real_mult (real_mult y z) (real_inv_pos y Hy))
                  (real_mult_assoc z y (real_inv_pos y Hy))
                  (RealSetoid.real_eq_mult_compat (real_mult z y)
                     (real_inv_pos y Hy) (real_mult y z)
                     (real_inv_pos y Hy)
                     (real_mult_comm z y)
                     (real_eq_refl (real_inv_pos y Hy))))
               (RealSetoid.real_eq_mult_compat (real_mult y z)
                  (real_inv_pos y Hy) real_one (real_inv_pos y Hy)
                  Hz
                  (real_eq_refl (real_inv_pos y Hy)))).
    + exact (real_eq_trans (real_mult real_one (real_inv_pos y Hy))
               (real_mult (real_inv_pos y Hy) real_one)
               (real_inv_pos y Hy)
               (real_mult_comm real_one (real_inv_pos y Hy))
               (real_mult_one (real_inv_pos y Hy))).
Qed.

(* of_nat 非负 / 严格正 / le 单调嵌入 *)
Lemma tvc_of_nat_nonneg : forall n : nat, real_le real_zero (real_of_nat n).
Proof.
  intro n. induction n as [| n IH].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat n))).
    + exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    + apply (real_le_plus_compat real_zero real_one real_zero (real_of_nat n)
               (tvd_lt_le real_zero real_one real_lt_zero_one) IH).
Qed.

Lemma tvc_of_nat_pos : forall n : nat,
  tvc_NatLt 0 n -> real_lt real_zero (real_of_nat n).
Proof.
  intros n Hn. destruct n as [| m].
  - exfalso. unfold tvc_NatLt in Hn. inversion Hn.
  - apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat m))
             (real_of_nat (Datatypes.S m))).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat m))).
      * exact (real_eq_sym (real_plus real_zero real_zero) real_zero
                 (real_plus_zero real_zero)).
      * exact (real_lt_plus_compat_lt_le real_zero real_one
                 real_zero (real_of_nat m)
                 real_lt_zero_one (tvc_of_nat_nonneg m)).
    + apply real_eq_refl.
Qed.

Lemma tvc_le_plus_nonneg_r : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb. destruct Hb as [Hlt | Heq].
  - apply tvd_lt_le.
    apply (RealSetoid.real_lt_id_r a (real_plus b a) (real_plus a b)
             (real_plus_comm b a)).
    apply (RealSetoid.real_lt_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_sym (real_plus real_zero a) a
                (tvd_plus_zero_l a))).
    exact (real_lt_plus_compat_lt_le real_zero b a a Hlt (real_le_refl a)).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_plus a b) a
             (real_eq_trans (real_plus a b) (real_plus a real_zero) a
                (RealSetoid.real_eq_plus_compat a b a real_zero
                   (real_eq_refl a) (real_eq_sym real_zero b Heq))
                (real_plus_zero a))).
Qed.

Lemma tvc_nat_le_embed : forall m n : nat,
  NatLe m n -> real_le (real_of_nat m) (real_of_nat n).
Proof.
  intros m n Hmn. pose proof (NatLe_drop m n Hmn) as Hmn'.
  clear Hmn. revert m Hmn'.
  induction n as [| n IH]; intros m Hm.
  - assert (Hm0 : m = 0%nat) by (inversion Hm; reflexivity).
    rewrite Hm0. apply real_le_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n)) as [Heq | Hne].
    + rewrite Heq. apply real_le_refl.
    + assert (Hmn2 : (m <= n)%nat).
      { inversion Hm; subst.
        - exfalso. apply Hne. reflexivity.
        - assumption. }
      apply (real_le_trans (real_of_nat m)
               (real_plus real_one (real_of_nat m))
               (real_plus real_one (real_of_nat n))).
      * apply (RealSetoid.real_le_id_r (real_of_nat m)
                 (real_plus (real_of_nat m) real_one)
                 (real_plus real_one (real_of_nat m))).
        -- exact (real_plus_comm (real_of_nat m) real_one).
        -- exact (tvc_le_plus_nonneg_r (real_of_nat m) real_one
                    (tvd_lt_le real_zero real_one real_lt_zero_one)).
      * exact (real_le_plus_compat real_one real_one (real_of_nat m)
                 (real_of_nat n) (real_le_refl real_one) (IH m Hmn2)).
Qed.

(* nat 幂交换：tv_rpow(of_nat k, n) == of_nat(k 的 n 次幂) *)
Lemma tvc_nat_rpow : forall k n : nat,
  real_eq (tv_rpow (real_of_nat k) n) (real_of_nat (k ^ n)).
Proof.
  intros k n. induction n as [| n IH].
  - exact (real_eq_sym (real_plus real_one real_zero) real_one
             (real_plus_zero real_one)).
  - apply (real_eq_trans (real_mult (real_of_nat k) (tv_rpow (real_of_nat k) n))
             (real_mult (real_of_nat k) (real_of_nat (k ^ n)))).
    + exact (RealSetoid.real_eq_mult_compat (real_of_nat k)
               (tv_rpow (real_of_nat k) n) (real_of_nat k)
               (real_of_nat (k ^ n)) (real_eq_refl (real_of_nat k)) IH).
    + exact (real_eq_sym _ _ (tvc_of_nat_mult k (k ^ n))).
Qed.

(* 幂对乘法的分裂：tv_rpow(a·b, n) == tv_rpow(a, n)·tv_rpow(b, n) *)
Lemma tvc_rpow_mult : forall (a b : Real) (n : nat),
  real_eq (tv_rpow (real_mult a b) n)
          (real_mult (tv_rpow a n) (tv_rpow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - exact (real_eq_sym real_one (real_mult real_one real_one)
             (real_mult_one real_one)).
  - apply (real_eq_trans
             (real_mult (real_mult a b) (tv_rpow (real_mult a b) n))
             (real_mult (real_mult a b)
                        (real_mult (tv_rpow a n) (tv_rpow b n)))).
    + exact (RealSetoid.real_eq_mult_compat (real_mult a b)
               (tv_rpow (real_mult a b) n) (real_mult a b)
               (real_mult (tv_rpow a n) (tv_rpow b n))
               (real_eq_refl (real_mult a b)) IH).
    + apply (real_eq_trans
               (real_mult (real_mult a b)
                          (real_mult (tv_rpow a n) (tv_rpow b n)))
               (real_mult a
                          (real_mult b
                             (real_mult (tv_rpow a n) (tv_rpow b n))))).
      * exact (real_eq_sym _ _
                 (real_mult_assoc a b
                    (real_mult (tv_rpow a n) (tv_rpow b n)))).
      * apply (real_eq_trans
                 (real_mult a
                            (real_mult b
                               (real_mult (tv_rpow a n) (tv_rpow b n))))
                 (real_mult a
                            (real_mult (real_mult b (tv_rpow a n))
                                       (tv_rpow b n)))).
        -- exact (RealSetoid.real_eq_mult_compat a
                     (real_mult b (real_mult (tv_rpow a n) (tv_rpow b n)))
                     a
                     (real_mult (real_mult b (tv_rpow a n)) (tv_rpow b n))
                     (real_eq_refl a)
                     (real_mult_assoc b (tv_rpow a n) (tv_rpow b n))).
        -- apply (real_eq_trans
                     (real_mult a
                                (real_mult (real_mult b (tv_rpow a n))
                                           (tv_rpow b n)))
                     (real_mult a
                                (real_mult (tv_rpow a n)
                                           (real_mult b (tv_rpow b n))))).
          ++ exact (RealSetoid.real_eq_mult_compat a
                       (real_mult (real_mult b (tv_rpow a n)) (tv_rpow b n))
                       a
                       (real_mult (tv_rpow a n) (real_mult b (tv_rpow b n)))
                       (real_eq_refl a)
                       (real_eq_trans
                          (real_mult (real_mult b (tv_rpow a n)) (tv_rpow b n))
                          (real_mult (real_mult (tv_rpow a n) b) (tv_rpow b n))
                          (real_mult (tv_rpow a n) (real_mult b (tv_rpow b n)))
                          (RealSetoid.real_eq_mult_compat
                             (real_mult b (tv_rpow a n)) (tv_rpow b n)
                             (real_mult (tv_rpow a n) b) (tv_rpow b n)
                             (real_mult_comm b (tv_rpow a n))
                             (real_eq_refl (tv_rpow b n)))
                          (real_eq_sym _ _
                             (real_mult_assoc (tv_rpow a n) b (tv_rpow b n))))).
          ++ exact (real_mult_assoc a (tv_rpow a n)
                       (real_mult b (tv_rpow b n))).
Qed.

(* 幂对逆的分裂：tv_rpow(inv x, n) == inv(tv_rpow x, n)；
   逆的正性证书 Hp 作显式槽（防 Qed 不透明常数上的换形）。
   路线：逆唯一性归约到 (x·x^n)·(inv x·(inv x)^n) == one 的因式装配链。 *)
Lemma tvc_rpow_inv : forall (x : Real) (Hx : real_lt real_zero x) (n : nat)
    (Hp : real_lt real_zero (tv_rpow x n)),
  real_eq (tv_rpow (real_inv_pos x Hx) n) (real_inv_pos (tv_rpow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - apply (real_eq_trans real_one
             (real_mult real_one (real_inv_pos real_one Hp))
             (real_inv_pos real_one Hp)).
    + exact (real_eq_sym _ _ (real_inv_pos_correct real_one Hp)).
    + exact (real_eq_trans (real_mult real_one (real_inv_pos real_one Hp))
               (real_mult (real_inv_pos real_one Hp) real_one)
               (real_inv_pos real_one Hp)
               (real_mult_comm real_one (real_inv_pos real_one Hp))
               (real_mult_one (real_inv_pos real_one Hp))).
  - specialize (IH (tvc_rpow_pos x Hx n)).
    pose proof (real_inv_pos_correct x Hx) as Hxi.
    pose proof (real_inv_pos_correct (tv_rpow x n) (tvc_rpow_pos x Hx n)) as Hbi.
    apply (tvc_inv_unique (real_mult x (tv_rpow x n))
             (real_mult (real_inv_pos x Hx) (tv_rpow (real_inv_pos x Hx) n)) Hp).
    apply (real_eq_trans
             (real_mult (real_mult x (tv_rpow x n))
                        (real_mult (real_inv_pos x Hx)
                                   (tv_rpow (real_inv_pos x Hx) n)))
             (real_mult (real_mult x (tv_rpow x n))
                        (real_mult (real_inv_pos x Hx)
                                   (real_inv_pos (tv_rpow x n)
                                      (tvc_rpow_pos x Hx n))))).
    + exact (RealSetoid.real_eq_mult_compat
               (real_mult x (tv_rpow x n))
               (real_mult (real_inv_pos x Hx) (tv_rpow (real_inv_pos x Hx) n))
               (real_mult x (tv_rpow x n))
               (real_mult (real_inv_pos x Hx)
                          (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n)))
               (real_eq_refl (real_mult x (tv_rpow x n)))
               (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx)
                  (tv_rpow (real_inv_pos x Hx) n)
                  (real_inv_pos x Hx)
                  (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))
                  (real_eq_refl (real_inv_pos x Hx)) IH)).
    + apply (real_eq_trans
               (real_mult (real_mult x (tv_rpow x n))
                          (real_mult (real_inv_pos x Hx)
                             (real_inv_pos (tv_rpow x n)
                                (tvc_rpow_pos x Hx n))))
               (real_mult x (real_mult (tv_rpow x n)
                          (real_mult (real_inv_pos x Hx)
                             (real_inv_pos (tv_rpow x n)
                                (tvc_rpow_pos x Hx n)))))).
      * exact (real_eq_sym _ _
                 (real_mult_assoc x (tv_rpow x n)
                    (real_mult (real_inv_pos x Hx)
                       (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))))).
      * apply (real_eq_trans _
                 (real_mult x (real_mult
                    (real_mult (tv_rpow x n) (real_inv_pos x Hx))
                    (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))))).
        -- exact (RealSetoid.real_eq_mult_compat x
                     (real_mult (tv_rpow x n)
                                (real_mult (real_inv_pos x Hx)
                                   (real_inv_pos (tv_rpow x n)
                                      (tvc_rpow_pos x Hx n))))
                     x
                     (real_mult (real_mult (tv_rpow x n) (real_inv_pos x Hx))
                                (real_inv_pos (tv_rpow x n)
                                   (tvc_rpow_pos x Hx n)))
                     (real_eq_refl x)
                     (real_mult_assoc (tv_rpow x n) (real_inv_pos x Hx)
                        (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n)))).
        -- apply (real_eq_trans _
                     (real_mult x (real_mult
                        (real_mult (real_inv_pos x Hx) (tv_rpow x n))
                        (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))))).
          ++ exact (RealSetoid.real_eq_mult_compat x
                       (real_mult
                          (real_mult (tv_rpow x n) (real_inv_pos x Hx))
                          (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n)))
                       x
                       (real_mult
                          (real_mult (real_inv_pos x Hx) (tv_rpow x n))
                          (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n)))
                       (real_eq_refl x)
                       (RealSetoid.real_eq_mult_compat
                          (real_mult (tv_rpow x n) (real_inv_pos x Hx))
                          (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))
                          (real_mult (real_inv_pos x Hx) (tv_rpow x n))
                          (real_inv_pos (tv_rpow x n) (tvc_rpow_pos x Hx n))
                          (real_mult_comm (tv_rpow x n) (real_inv_pos x Hx))
                          (real_eq_refl
                             (real_inv_pos (tv_rpow x n)
                                (tvc_rpow_pos x Hx n))))).
          ++ apply (real_eq_trans _
                       (real_mult x (real_mult (real_inv_pos x Hx)
                          (real_mult (tv_rpow x n)
                             (real_inv_pos (tv_rpow x n)
                                (tvc_rpow_pos x Hx n)))))).
            ** exact (RealSetoid.real_eq_mult_compat x
                        (real_mult (real_mult (real_inv_pos x Hx)
                                         (tv_rpow x n))
                                   (real_inv_pos (tv_rpow x n)
                                      (tvc_rpow_pos x Hx n)))
                        x
                        (real_mult (real_inv_pos x Hx)
                                   (real_mult (tv_rpow x n)
                                              (real_inv_pos (tv_rpow x n)
                                                 (tvc_rpow_pos x Hx n))))
                        (real_eq_refl x)
                        (real_eq_sym _ _
                           (real_mult_assoc (real_inv_pos x Hx) (tv_rpow x n)
                              (real_inv_pos (tv_rpow x n)
                                 (tvc_rpow_pos x Hx n))))).
            ** apply (real_eq_trans _
                          (real_mult (real_mult x (real_inv_pos x Hx))
                             (real_mult (tv_rpow x n)
                                        (real_inv_pos (tv_rpow x n)
                                           (tvc_rpow_pos x Hx n))))).
               --- exact (real_mult_assoc x (real_inv_pos x Hx)
                             (real_mult (tv_rpow x n)
                                        (real_inv_pos (tv_rpow x n)
                                           (tvc_rpow_pos x Hx n)))).
               --- apply (real_eq_trans _
                             (real_mult real_one
                                (real_mult (tv_rpow x n)
                                           (real_inv_pos (tv_rpow x n)
                                              (tvc_rpow_pos x Hx n))))).
                    +++ exact (RealSetoid.real_eq_mult_compat
                                  (real_mult x (real_inv_pos x Hx))
                                  (real_mult (tv_rpow x n)
                                             (real_inv_pos (tv_rpow x n)
                                                (tvc_rpow_pos x Hx n)))
                                  real_one
                                  (real_mult (tv_rpow x n)
                                             (real_inv_pos (tv_rpow x n)
                                                (tvc_rpow_pos x Hx n)))
                                  Hxi
                                  (real_eq_refl
                                     (real_mult (tv_rpow x n)
                                        (real_inv_pos (tv_rpow x n)
                                           (tvc_rpow_pos x Hx n))))).
                    +++ apply (real_eq_trans _
                                  (real_mult (tv_rpow x n)
                                             (real_inv_pos (tv_rpow x n)
                                                (tvc_rpow_pos x Hx n)))).
                        *** exact (tvc_mult_one_l
                                      (real_mult (tv_rpow x n)
                                         (real_inv_pos (tv_rpow x n)
                                            (tvc_rpow_pos x Hx n)))).
                        *** exact Hbi.
Qed.

(* ################ Part 1：tvd 接口面步数计算器（TVRealWorld 映像） ######## *)
(*   证书子集映像（tv_doeblin_iter 闭包 8 证书经 repl 实拍，K_pos/delta_pos/
     n_pos 被闭包裁剪故仅 delta_pos 作率证书补槽）；几何击破证书 omd_arch
     为接口显式携带（任意实数率的构造性 ceil 桥为开放矿脉，S04 r_arch_pow/
     S06 r_arch_pow_attn 在役同款）。                                        *)
(* ######################################################################## *)

Lemma tvc_omd_rate_pos : forall delta : Real,
  real_lt delta real_one -> real_lt real_zero (tv_omd delta).
Proof. intros delta H. exact (tv_omd_pos_of_lt delta H). Qed.

Lemma tvc_omd_rate_lt_one : forall delta : Real,
  real_lt real_zero delta -> real_lt (tv_omd delta) real_one.
Proof. intros delta H. exact (mix_omd_lt_one delta H). Qed.

Section TvcTvdStepCalc.

Variable states : list (list Real).
Variable K : list Real -> list Real -> Real.
Variable K_row : forall i : list Real,
  real_eq (real_list_sum (list Real) (K i) states) real_one.
Variable u : list Real -> Real.
Variable u_norm : real_eq (real_list_sum (list Real) u states) real_one.
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_lt_one : real_lt delta real_one.
Variable minorization : forall i j : list Real,
  real_le (real_mult delta (u j)) (K i j).
Variable abs_sum_le_list : forall f : list Real -> Real,
  real_le (real_abs (real_list_sum (list Real) f states))
          (real_list_sum (list Real)
             (fun w : list Real => real_abs (f w)) states).
(* 几何击破证书（接口显式携带；实参化接口假设、非公理——PA Closed 实证） *)
Variable omd_arch : forall (a eps : Real),
  real_lt real_zero a -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a (tv_rpow (tv_omd delta) N)) eps).

Let omd : Real := tv_omd delta.

(* ===== Defined 步数计算器（精度→步数） ===== *)

Definition tvc_step_calc (TV0 : Real) (HTV0 : real_lt real_zero TV0)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (omd_arch TV0 eps HTV0 Heps).

(* 正确性半 1：几何率预算面 *)
Theorem tvc_step_calc_budget : forall (TV0 : Real)
  (HTV0 : real_lt real_zero TV0) (eps : Real) (Heps : real_lt real_zero eps),
  real_lt (real_mult TV0
             (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps))) eps.
Proof.
  intros TV0 HTV0 eps Heps. exact (projT2 (omd_arch TV0 eps HTV0 Heps)).
Qed.

(* 正确性半 2：TV 迭代面——步数读数 N 之后任意步 n、任意归一化对、
   TV 不超初值 TV0，则 TV(iter^n) < eps（使用 tv_doeblin_iter 闭包） *)
Theorem tvc_step_calc_correct : forall (TV0 : Real)
  (HTV0 : real_lt real_zero TV0) (eps : Real) (Heps : real_lt real_zero eps)
  (mu nu : list Real -> Real)
  (Hmu : real_eq (real_list_sum (list Real) mu states) real_one)
  (Hnu : real_eq (real_list_sum (list Real) nu states) real_one)
  (HTV : real_le (tv_doeblin states mu nu) TV0) (n : nat),
  NatLe (tvc_step_calc TV0 HTV0 eps Heps) n ->
  real_lt (tv_doeblin states (tv_titer states K n mu)
             (tv_titer states K n nu)) eps.
Proof.
  intros TV0 HTV0 eps Heps mu nu Hmu Hnu HTV n Hn.
  pose proof (tv_doeblin_iter states K K_row u u_norm delta
               (tvd_lt_le delta real_one delta_lt_one)
               minorization abs_sum_le_list n mu nu Hmu Hnu) as Hdec.
  pose proof (tvc_rpow_dec_iter omd
               (tvc_omd_rate_pos delta delta_lt_one)
               (tvd_lt_le omd real_one
                  (tvc_omd_rate_lt_one delta delta_pos))
               (tvc_step_calc TV0 HTV0 eps Heps) n Hn) as Hmono.
  pose proof (tvc_step_calc_budget TV0 HTV0 eps Heps) as Hbud0.
  apply (real_le_lt_trans
           (tv_doeblin states (tv_titer states K n mu)
                       (tv_titer states K n nu))
           (real_mult (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps)) TV0)
           eps).
  - apply (real_le_trans
             (tv_doeblin states (tv_titer states K n mu)
                         (tv_titer states K n nu))
             (real_mult (tv_rpow omd n) (tv_doeblin states mu nu))
             (real_mult (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps)) TV0)).
    + exact Hdec.
    + apply (real_le_trans
               (real_mult (tv_rpow omd n) (tv_doeblin states mu nu))
               (real_mult (tv_rpow omd n) TV0)
               (real_mult (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps)) TV0)).
      * exact (real_le_mult_compat_r (tv_rpow omd n)
                   (tv_doeblin states mu nu) TV0
                   (tvd_lt_le real_zero (tv_rpow omd n)
                      (tvc_rpow_pos omd (tvc_omd_rate_pos delta delta_lt_one)
                         n))
                   HTV).
      * exact (real_le_mult_compat (tv_rpow omd n)
                   (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps))
                   TV0 HTV0 Hmono).
  - exact (RealSetoid.real_lt_id_l
             (real_mult (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps)) TV0)
             (real_mult TV0
                (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps)))
             eps
             (real_mult_comm (tv_rpow omd (tvc_step_calc TV0 HTV0 eps Heps))
                TV0)
             Hbud0).
Qed.

(* sigT 混合时间模量（Defined）：精度→步数见证的 Set 形居住 *)
Theorem tvc_mixing_modulus_sigT : forall (TV0 eps : Real)
  (HTV0 : real_lt real_zero TV0) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (mu nu : list Real -> Real),
        real_eq (real_list_sum (list Real) mu states) real_one ->
        real_eq (real_list_sum (list Real) nu states) real_one ->
        real_le (tv_doeblin states mu nu) TV0 ->
        forall n : nat, NatLe N n ->
        real_lt (tv_doeblin states (tv_titer states K n mu)
                   (tv_titer states K n nu)) eps).
Proof.
  intros TV0 eps HTV0 Heps. exists (tvc_step_calc TV0 HTV0 eps Heps).
  exact (tvc_step_calc_correct TV0 HTV0 eps Heps).
Defined.

End TvcTvdStepCalc.

(* ################ Part 1b：tvd 实例面（delta-star := e^{−2γ/T}） ########## *)
(*   实例层新证：delta-star < 1 严格面（原档仅 le 版 tvd_dstar_le_one）；
     计算器与 sigT 模量以显式率 (1 − e^{−2γ/T}) 消解主迭代件
     tvd_dstar_iter_contraction（14 实参闭包经 repl 实拍）。                   *)
(* ######################################################################## *)

Lemma tvc_dstar_lt_one : forall (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
    (gamma : Real) (gamma_pos : real_lt real_zero gamma),
  real_lt (tvd_dstar Ttemp Ttemp_pos gamma) real_one.
Proof.
  intros Ttemp Ttemp_pos gamma gamma_pos.
  assert (Hkey : real_lt
                   (real_exp_neg
                      (real_plus (tvd_tg Ttemp Ttemp_pos gamma)
                                 (tvd_tg Ttemp Ttemp_pos gamma)))
                   (real_exp_neg real_zero)).
  { apply (real_exp_neg_decr real_zero
             (real_plus (tvd_tg Ttemp Ttemp_pos gamma)
                        (tvd_tg Ttemp Ttemp_pos gamma))).
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (tvd_tg Ttemp Ttemp_pos gamma)
                        (tvd_tg Ttemp Ttemp_pos gamma))).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat_lt_le real_zero
               (tvd_tg Ttemp Ttemp_pos gamma)
               real_zero (tvd_tg Ttemp Ttemp_pos gamma)
               (tvd_tg_pos Ttemp Ttemp_pos gamma gamma_pos)
               (tvd_lt_le real_zero (tvd_tg Ttemp Ttemp_pos gamma)
                  (tvd_tg_pos Ttemp Ttemp_pos gamma gamma_pos))). }
  apply (real_lt_eq_lt (tvd_dstar Ttemp Ttemp_pos gamma)
           (real_exp_neg real_zero) real_one).
  - exact Hkey.
  - exact tvd_exp_neg_zero.
Qed.

Section TvcTvdDstarCalc.

Variable states : list (list Real).
Variable n_pos : real_lt real_zero (real_of_nat (length states)).
Variable Ttemp : Real.
Variable Ttemp_pos : real_lt real_zero Ttemp.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable z : list Real -> list Real -> Real.
Variable z_lo : forall i j : list Real, real_le (real_opp gamma) (z i j).
Variable z_hi : forall i j : list Real, real_le (z i j) gamma.
Variable abs_sum_le_list : forall f : list Real -> Real,
  real_le (real_abs (real_list_sum (list Real) f states))
          (real_list_sum (list Real)
             (fun w : list Real => real_abs (f w)) states).
(* 实例层几何击破证书（接口显式携带，同 Part 1 判定） *)
Variable dstar_arch : forall (a eps : Real),
  real_lt real_zero a -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
               (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) N)) eps).

Let t_dst : Real := tvd_dstar Ttemp Ttemp_pos gamma.
Let omd_dst : Real := tv_omd t_dst.
Let K_dst : list Real -> list Real -> Real :=
  tvd_K states n_pos Ttemp Ttemp_pos z.
Let u_dst : list Real -> Real := tvd_u states n_pos.

Lemma tvc_dstar_rate_pos : real_lt real_zero omd_dst.
Proof. exact (tv_omd_pos_of_lt t_dst (tvc_dstar_lt_one Ttemp Ttemp_pos gamma gamma_pos)). Qed.

Lemma tvc_dstar_rate_lt_one : real_lt omd_dst real_one.
Proof. exact (mix_omd_lt_one t_dst (tvd_dstar_pos Ttemp Ttemp_pos gamma)). Qed.

(* ===== Defined 步数计算器（实例面） ===== *)

Definition tvc_dstar_step_calc (TV0 : Real) (HTV0 : real_lt real_zero TV0)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (dstar_arch TV0 eps HTV0 Heps).

Theorem tvc_dstar_step_calc_budget : forall (TV0 : Real)
  (HTV0 : real_lt real_zero TV0) (eps : Real) (Heps : real_lt real_zero eps),
  real_lt (real_mult TV0
             (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps))) eps.
Proof.
  intros TV0 HTV0 eps Heps. exact (projT2 (dstar_arch TV0 eps HTV0 Heps)).
Qed.

(* 正确性：使用 tvd_dstar_iter_contraction（显式率 (1 − e^{−2γ/T})^n） *)
Theorem tvc_dstar_step_calc_correct : forall (TV0 : Real)
  (HTV0 : real_lt real_zero TV0) (eps : Real) (Heps : real_lt real_zero eps)
  (mu nu : list Real -> Real)
  (Hmu : real_eq (real_list_sum (list Real) mu states) real_one)
  (Hnu : real_eq (real_list_sum (list Real) nu states) real_one)
  (HTV : real_le (tv_doeblin states mu nu) TV0) (n : nat),
  NatLe (tvc_dstar_step_calc TV0 HTV0 eps Heps) n ->
  real_lt (tv_doeblin states (tv_titer states K_dst n mu)
             (tv_titer states K_dst n nu)) eps.
Proof.
  intros TV0 HTV0 eps Heps mu nu Hmu Hnu HTV n Hn.
  pose proof (tvd_dstar_iter_contraction states n_pos Ttemp Ttemp_pos gamma
               gamma_pos z z_lo z_hi abs_sum_le_list n mu nu Hmu Hnu) as Hdec.
  pose proof (tvc_rpow_dec_iter omd_dst tvc_dstar_rate_pos
               (tvd_lt_le omd_dst real_one tvc_dstar_rate_lt_one)
               (tvc_dstar_step_calc TV0 HTV0 eps Heps) n Hn) as Hmono.
  pose proof (tvc_dstar_step_calc_budget TV0 HTV0 eps Heps) as Hbud0.
  apply (real_le_lt_trans
           (tv_doeblin states (tv_titer states K_dst n mu)
                       (tv_titer states K_dst n nu))
           (real_mult (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps))
                      TV0)
           eps).
  - apply (real_le_trans
             (tv_doeblin states (tv_titer states K_dst n mu)
                         (tv_titer states K_dst n nu))
             (real_mult (tv_rpow omd_dst n) (tv_doeblin states mu nu))
             (real_mult (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps))
                        TV0)).
    + exact Hdec.
    + apply (real_le_trans
               (real_mult (tv_rpow omd_dst n) (tv_doeblin states mu nu))
               (real_mult (tv_rpow omd_dst n) TV0)
               (real_mult (tv_rpow omd_dst
                              (tvc_dstar_step_calc TV0 HTV0 eps Heps)) TV0)).
      * exact (real_le_mult_compat_r (tv_rpow omd_dst n)
                   (tv_doeblin states mu nu) TV0
                   (tvd_lt_le real_zero (tv_rpow omd_dst n)
                      (tvc_rpow_pos omd_dst tvc_dstar_rate_pos n))
                   HTV).
      * exact (real_le_mult_compat (tv_rpow omd_dst n)
                   (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps))
                   TV0 HTV0 Hmono).
  - exact (RealSetoid.real_lt_id_l
             (real_mult (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps))
                TV0)
             (real_mult TV0
                (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps)))
             eps
             (real_mult_comm
                (tv_rpow omd_dst (tvc_dstar_step_calc TV0 HTV0 eps Heps)) TV0)
             Hbud0).
Qed.

(* sigT 混合时间模量（实例面，Defined） *)
Theorem tvc_dstar_mixing_sigT : forall (TV0 eps : Real)
  (HTV0 : real_lt real_zero TV0) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (mu nu : list Real -> Real),
        real_eq (real_list_sum (list Real) mu states) real_one ->
        real_eq (real_list_sum (list Real) nu states) real_one ->
        real_le (tv_doeblin states mu nu) TV0 ->
        forall n : nat, NatLe N n ->
        real_lt (tv_doeblin states (tv_titer states K_dst n mu)
                   (tv_titer states K_dst n nu)) eps).
Proof.
  intros TV0 eps HTV0 Heps. exists (tvc_dstar_step_calc TV0 HTV0 eps Heps).
  exact (tvc_dstar_step_calc_correct TV0 HTV0 eps Heps).
Defined.

End TvcTvdDstarCalc.

(* ################ Part 3 主件：定点档读数的有理数据实面正确性 ############ *)

(* 几何装配 Id 面：A·(p/q)^N == (A·p^N)·q^{-N} *)
Lemma tvc_geom_lhs_id : forall (A p q : nat)
    (Hqr : real_lt real_zero (real_of_nat q)) (N : nat),
  real_eq (real_mult (real_of_nat A)
             (tv_rpow (real_mult (real_of_nat p)
                       (real_inv_pos (real_of_nat q) Hqr)) N))
          (real_mult (real_mult (real_of_nat A) (real_of_nat (p ^ N)))
             (real_inv_pos (tv_rpow (real_of_nat q) N)
                (tvc_rpow_pos (real_of_nat q) Hqr N))).
Proof.
  intros A p q Hqr N.
  pose proof (tvc_rpow_mult (real_of_nat p) (real_inv_pos (real_of_nat q) Hqr) N)
    as Hpm.
  pose proof (tvc_nat_rpow p N) as Hpo.
  pose proof (tvc_rpow_inv (real_of_nat q) Hqr N
                (tvc_rpow_pos (real_of_nat q) Hqr N)) as Hpi.
  assert (Hs2 : real_eq
                  (real_mult (tv_rpow (real_of_nat p) N)
                              (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))
                  (real_mult (real_of_nat (p ^ N))
                              (real_inv_pos (tv_rpow (real_of_nat q) N)
                                 (tvc_rpow_pos (real_of_nat q) Hqr N)))).
  { apply (real_eq_trans
             (real_mult (tv_rpow (real_of_nat p) N)
                        (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))
             (real_mult (real_of_nat (p ^ N))
                        (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))).
    - exact (RealSetoid.real_eq_mult_compat (tv_rpow (real_of_nat p) N)
               (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N)
               (real_of_nat (p ^ N))
               (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N)
               Hpo
               (real_eq_refl (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))).
    - exact (RealSetoid.real_eq_mult_compat (real_of_nat (p ^ N))
               (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N)
               (real_of_nat (p ^ N))
               (real_inv_pos (tv_rpow (real_of_nat q) N)
                  (tvc_rpow_pos (real_of_nat q) Hqr N))
               (real_eq_refl (real_of_nat (p ^ N))) Hpi). }
  apply (real_eq_trans
           (real_mult (real_of_nat A)
                      (tv_rpow (real_mult (real_of_nat p)
                                (real_inv_pos (real_of_nat q) Hqr)) N))
           (real_mult (real_of_nat A)
                      (real_mult (tv_rpow (real_of_nat p) N)
                                 (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N)))).
  - exact (RealSetoid.real_eq_mult_compat (real_of_nat A)
             (tv_rpow (real_mult (real_of_nat p)
                       (real_inv_pos (real_of_nat q) Hqr)) N)
             (real_of_nat A)
             (real_mult (tv_rpow (real_of_nat p) N)
                        (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))
             (real_eq_refl (real_of_nat A)) Hpm).
  - apply (real_eq_trans
             (real_mult (real_of_nat A)
                        (real_mult (tv_rpow (real_of_nat p) N)
                                   (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N)))
             (real_mult (real_of_nat A)
                        (real_mult (real_of_nat (p ^ N))
                                   (real_inv_pos (tv_rpow (real_of_nat q) N)
                                      (tvc_rpow_pos (real_of_nat q) Hqr N))))).
    + exact (RealSetoid.real_eq_mult_compat (real_of_nat A)
               (real_mult (tv_rpow (real_of_nat p) N)
                          (tv_rpow (real_inv_pos (real_of_nat q) Hqr) N))
               (real_of_nat A)
               (real_mult (real_of_nat (p ^ N))
                          (real_inv_pos (tv_rpow (real_of_nat q) N)
                             (tvc_rpow_pos (real_of_nat q) Hqr N)))
               (real_eq_refl (real_of_nat A)) Hs2).
    + exact (real_mult_assoc (real_of_nat A) (real_of_nat (p ^ N))
               (real_inv_pos (tv_rpow (real_of_nat q) N)
                  (tvc_rpow_pos (real_of_nat q) Hqr N))).
Qed.

(* 几何装配 Id 面：(E·q^N)·q^{-N} == E *)
Lemma tvc_geom_rhs_id : forall (E q : nat)
    (Hqr : real_lt real_zero (real_of_nat q)) (N : nat),
  real_eq (real_mult (real_mult (real_of_nat E) (real_of_nat (q ^ N)))
             (real_inv_pos (tv_rpow (real_of_nat q) N)
                (tvc_rpow_pos (real_of_nat q) Hqr N)))
          (real_of_nat E).
Proof.
  intros E q Hqr N.
  apply (real_eq_trans
           (real_mult (real_mult (real_of_nat E) (real_of_nat (q ^ N)))
                      (real_inv_pos (tv_rpow (real_of_nat q) N)
                         (tvc_rpow_pos (real_of_nat q) Hqr N)))
           (real_mult (real_of_nat E)
                      (real_mult (real_of_nat (q ^ N))
                                 (real_inv_pos (tv_rpow (real_of_nat q) N)
                                    (tvc_rpow_pos (real_of_nat q) Hqr N))))).
  - exact (real_eq_sym _ _
             (real_mult_assoc (real_of_nat E) (real_of_nat (q ^ N))
                (real_inv_pos (tv_rpow (real_of_nat q) N)
                   (tvc_rpow_pos (real_of_nat q) Hqr N)))).
  - apply (real_eq_trans
             (real_mult (real_of_nat E)
                        (real_mult (real_of_nat (q ^ N))
                                   (real_inv_pos (tv_rpow (real_of_nat q) N)
                                      (tvc_rpow_pos (real_of_nat q) Hqr N))))
             (real_mult (real_of_nat E)
                        (real_mult (tv_rpow (real_of_nat q) N)
                                   (real_inv_pos (tv_rpow (real_of_nat q) N)
                                      (tvc_rpow_pos (real_of_nat q) Hqr N))))).
    + exact (RealSetoid.real_eq_mult_compat (real_of_nat E)
               (real_mult (real_of_nat (q ^ N))
                          (real_inv_pos (tv_rpow (real_of_nat q) N)
                             (tvc_rpow_pos (real_of_nat q) Hqr N)))
               (real_of_nat E)
               (real_mult (tv_rpow (real_of_nat q) N)
                          (real_inv_pos (tv_rpow (real_of_nat q) N)
                             (tvc_rpow_pos (real_of_nat q) Hqr N)))
               (real_eq_refl (real_of_nat E))
               (RealSetoid.real_eq_mult_compat (real_of_nat (q ^ N))
                  (real_inv_pos (tv_rpow (real_of_nat q) N)
                     (tvc_rpow_pos (real_of_nat q) Hqr N))
                  (tv_rpow (real_of_nat q) N)
                  (real_inv_pos (tv_rpow (real_of_nat q) N)
                     (tvc_rpow_pos (real_of_nat q) Hqr N))
                  (real_eq_sym _ _ (tvc_nat_rpow q N))
                  (real_eq_refl
                     (real_inv_pos (tv_rpow (real_of_nat q) N)
                        (tvc_rpow_pos (real_of_nat q) Hqr N))))).
    + apply (real_eq_trans
               (real_mult (real_of_nat E)
                          (real_mult (tv_rpow (real_of_nat q) N)
                                     (real_inv_pos (tv_rpow (real_of_nat q) N)
                                        (tvc_rpow_pos (real_of_nat q) Hqr N))))
               (real_mult (real_of_nat E) real_one)).
      * exact (RealSetoid.real_eq_mult_compat (real_of_nat E)
                 (real_mult (tv_rpow (real_of_nat q) N)
                            (real_inv_pos (tv_rpow (real_of_nat q) N)
                               (tvc_rpow_pos (real_of_nat q) Hqr N)))
                 (real_of_nat E) real_one
                 (real_eq_refl (real_of_nat E))
                 (real_inv_pos_correct (tv_rpow (real_of_nat q) N)
                    (tvc_rpow_pos (real_of_nat q) Hqr N))).
      * exact (real_mult_one (real_of_nat E)).
Qed.

(* 定点档主件（le 档）：有理数据 kappa = p/q 上，严格档枚举读数 N 满足
   实面 le (A·kappa^N) E（Set 形陈述，零 arch 依赖） *)
Theorem tvc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : real_lt real_zero (real_of_nat q)),
  NatLe 1 p -> NatLe 1 q ->
  tvc_reach fuel p q A E ->
  real_le (real_mult (real_of_nat A)
             (tv_rpow (real_mult (real_of_nat p)
                       (real_inv_pos (real_of_nat q) Hqr))
                (tvc_k_enum fuel p q A E)))
          (real_of_nat E).
Proof.
  intros fuel p q A E Hqr Hp Hq Hterm.
  pose proof (tvc_k_enum_ltface fuel p q A E Hp Hq Hterm) as Hltf.
  assert (Hle2 : NatLe (A * p ^ tvc_k_enum fuel p q A E)
                   (E * q ^ tvc_k_enum fuel p q A E)).
  { apply NatLe_lift. pose proof (NatLe_drop _ _ Hltf) as Hlog'. lia. }
  pose proof (tvc_nat_le_embed (A * p ^ tvc_k_enum fuel p q A E)
                (E * q ^ tvc_k_enum fuel p q A E) Hle2) as Hemb.
  pose proof (tvc_of_nat_mult A (p ^ tvc_k_enum fuel p q A E)) as Hm1.
  pose proof (tvc_of_nat_mult E (q ^ tvc_k_enum fuel p q A E)) as Hm2.
  assert (Hsplit : real_le
                     (real_mult (real_of_nat A)
                        (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
                     (real_mult (real_of_nat E)
                        (real_of_nat (q ^ tvc_k_enum fuel p q A E)))).
  { apply (RealSetoid.real_le_id_l
             (real_mult (real_of_nat A) (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
             (real_of_nat (A * p ^ tvc_k_enum fuel p q A E))).
    - exact (real_eq_sym _ _ Hm1).
    - apply (RealSetoid.real_le_id_r
               (real_of_nat (A * p ^ tvc_k_enum fuel p q A E))
               (real_of_nat (E * q ^ tvc_k_enum fuel p q A E))
               (real_mult (real_of_nat E)
                  (real_of_nat (q ^ tvc_k_enum fuel p q A E)))).
      + exact Hm2.
      + exact Hemb. }
  assert (H3 : real_le
                 (real_mult (real_mult (real_of_nat A)
                            (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
                             (real_inv_pos (tv_rpow (real_of_nat q)
                                (tvc_k_enum fuel p q A E))
                                (tvc_rpow_pos (real_of_nat q) Hqr
                                   (tvc_k_enum fuel p q A E))))
                 (real_mult (real_mult (real_of_nat E)
                            (real_of_nat (q ^ tvc_k_enum fuel p q A E)))
                             (real_inv_pos (tv_rpow (real_of_nat q)
                                (tvc_k_enum fuel p q A E))
                                (tvc_rpow_pos (real_of_nat q) Hqr
                                   (tvc_k_enum fuel p q A E))))).
  { exact (real_le_mult_compat
             (real_mult (real_of_nat A) (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
             (real_mult (real_of_nat E) (real_of_nat (q ^ tvc_k_enum fuel p q A E)))
             (real_inv_pos (tv_rpow (real_of_nat q) (tvc_k_enum fuel p q A E))
                (tvc_rpow_pos (real_of_nat q) Hqr (tvc_k_enum fuel p q A E)))
             (real_inv_pos_pos (tv_rpow (real_of_nat q) (tvc_k_enum fuel p q A E))
                (tvc_rpow_pos (real_of_nat q) Hqr (tvc_k_enum fuel p q A E)))
             Hsplit). }
  apply (RealSetoid.real_le_id_l
           (real_mult (real_of_nat A)
              (tv_rpow (real_mult (real_of_nat p)
                        (real_inv_pos (real_of_nat q) Hqr))
                 (tvc_k_enum fuel p q A E)))
           (real_mult (real_mult (real_of_nat A)
                       (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
                      (real_inv_pos (tv_rpow (real_of_nat q)
                         (tvc_k_enum fuel p q A E))
                         (tvc_rpow_pos (real_of_nat q) Hqr
                            (tvc_k_enum fuel p q A E))))).
  - exact (tvc_geom_lhs_id A p q Hqr (tvc_k_enum fuel p q A E)).
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_mult (real_of_nat A)
                         (real_of_nat (p ^ tvc_k_enum fuel p q A E)))
                        (real_inv_pos (tv_rpow (real_of_nat q)
                           (tvc_k_enum fuel p q A E))
                           (tvc_rpow_pos (real_of_nat q) Hqr
                              (tvc_k_enum fuel p q A E))))
             (real_mult (real_mult (real_of_nat E)
                         (real_of_nat (q ^ tvc_k_enum fuel p q A E)))
                        (real_inv_pos (tv_rpow (real_of_nat q)
                           (tvc_k_enum fuel p q A E))
                           (tvc_rpow_pos (real_of_nat q) Hqr
                              (tvc_k_enum fuel p q A E))))
             (real_of_nat E)).
    + exact (tvc_geom_rhs_id E q Hqr (tvc_k_enum fuel p q A E)).
    + exact H3.
Qed.

(* 定点档 omd 直连版：omd == p/q 证书下，枚举读数 N 满足实面
   le (A·omd^N) E——计算器读数直供率预算（换底经 tvc_rpow_wd 一跳） *)
Theorem tvc_omd_enum_budget : forall (fuel p q A E : nat)
  (Hqr : real_lt real_zero (real_of_nat q)) (omd : Real),
  NatLe 1 p -> NatLe 1 q ->
  real_eq omd (real_mult (real_of_nat p) (real_inv_pos (real_of_nat q) Hqr)) ->
  tvc_reach fuel p q A E ->
  real_le (real_mult (real_of_nat A) (tv_rpow omd (tvc_k_enum fuel p q A E)))
          (real_of_nat E).
Proof.
  intros fuel p q A E Hqr omd Hp Hq Homd Hterm.
  apply (RealSetoid.real_le_id_l
           (real_mult (real_of_nat A) (tv_rpow omd (tvc_k_enum fuel p q A E)))
           (real_mult (real_of_nat A)
              (tv_rpow (real_mult (real_of_nat p)
                        (real_inv_pos (real_of_nat q) Hqr))
                 (tvc_k_enum fuel p q A E)))).
  - exact (RealSetoid.real_eq_mult_compat (real_of_nat A)
             (tv_rpow omd (tvc_k_enum fuel p q A E))
             (real_of_nat A)
             (tv_rpow (real_mult (real_of_nat p)
                       (real_inv_pos (real_of_nat q) Hqr))
                (tvc_k_enum fuel p q A E))
             (real_eq_refl (real_of_nat A))
             (tvc_rpow_wd omd
                (real_mult (real_of_nat p) (real_inv_pos (real_of_nat q) Hqr))
                (tvc_k_enum fuel p q A E) Homd)).
  - exact (tvc_enum_real_correct fuel p q A E Hqr Hp Hq Hterm).
Qed.

(* ################ G4 审计口：公理面与可提取强证 ########################## *)

Print Assumptions tvc_k_enum_ltface.
Print Assumptions tvc_reach_gen.
Print Assumptions tvc_k_enum_auto_half.
Print Assumptions tvc_k_enum_auto_qbound.
Print Assumptions tvc_step_calc_budget.
Print Assumptions tvc_step_calc_correct.
Print Assumptions tvc_mixing_modulus_sigT.
Print Assumptions tvc_dstar_lt_one.
Print Assumptions tvc_dstar_mixing_sigT.
Print Assumptions tvc_enum_real_correct.
Print Assumptions tvc_omd_enum_budget.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction tvc_ceil_div tvc_iter tvc_pow_iter tvc_k_enum.
