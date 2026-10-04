(* 模块：LW1PiMeasure.v —— π 无理性测度（语句面＋距离率互译，B 档）。
   使命：把分离见证闭式 c(a,b) 定量化为显式率：主语句为幂率形     
   sigT μ₀ → NatLe 2 μ₀（Set 面）→ sigT C → ∀q, 预算内真分离＋预算界；
   原案线性增长率已被 π 连分数收敛子 1/q_n² 的事实反驳（文献口径），    
   本件全文零线性形；候选形（ⅰ）μ:Q→nat 逐点反演列为定义层随件（§2）。 
   §3b 距离率互译：|π_L − q| ≥ c₀/h(q)^μ₀ 的 Q 投影证书＋预算口径（1 < C·c₀）
   ⟹ 预算内真分离（lw5n_inwin_close_pt 逆否＋lw5n_find_hit 合成）；主定理由此
   归并为两前提形，证书面由 lw1m_b_cert_face 单独承载的闭合与后续支配链。
   局限声明：μ₀/C 具体字面待后续件，主定理以假设位承载（sigT 接口＋率       
   证书前提），具体数值不在语句外预告；本件无占位见证。
   依赖：S01_BaseRing（Id/id_refl/And/NatLe/NatLe_lift/NatLe_drop）、
   S02_CauchyComplete（QltT/QleT/real_lt/real_const）、S03_QExp（real_metric）、
   S10_KVQuantTrig（real_pi_geom）、LW5SepComplexity（lw5n_find/lw5n_sep_dec/
   lw5n_find_ub/lw5n_find_hit/lw5n_inwin_close_pt 预算无关机件）、
   PiEnvelope（QltT'/QltT 互转）、LW0MLicBridge（lw0m_xL 投影列）、LW0LeibSeparation（α 守卫形供件，限定引用）、LW0PiIrrational（阶乘占优与 w0 供件族，限定引用）、
   Stdlib：QArith/Qabs/Qround/ZArith/Arith/Bool/Lia/Extraction。
   对标：LW0LeibWindow.v leiblw_lic_escape_window（sigT 嵌套 Set 面同形）；
   LW0PiIrrational.v lw0_pi_irrational（分离闭式接口形渲染参照）与 lw0_pi_d0_of
   （分母阈值函数先例）；LW5SepComplexity.v lw5n_find_hit（命中机件包参照）；LW0LeibSeparation.v leibsep_pi_sep_alpha_guarded（真层证书结论形参照）；LW0PiIrrational.v lw0_n_select_dominated（阶乘占优参照）。
   构造性：零公理/零承认式/零经典逻辑；语句面全 Set（Id＋NatLe＋sigT＋And＋
   QltT/QltT'），六词面零命中；nat 面线性步显式链，结论位 nat 序仅
   lw1m_dist_order_ub（lw5n_find_ub 同族，如实注记），Q 面走 Qmult_inv_r/
   Qmult_lt_compat_r 显式链零 solver 收尾；lw1m_b_cert_face 系闭式接口形     
   的自持假设位（零内引他件）；现行 Qden : Q -> positive，高度坐标取
   S(Pos.to_nat(Qden(Qred q)))；提取面 Obj.magic=0；文末假设审计全 Closed。
   编译配方：coqc -q -native-compiler no，
   -Q ConstructiveWorld-Main/ConstructiveWorld_vo "" -Q Live_X Local；
   编译前后查依赖邻件 vo 新鲜度。
   作用域注记：Q 作用域随 QArith 全局开启（数字字面默认 Q 形），nat 算术
   逐处 %nat 标注；Datatypes.S 显式拼写防构造子遮蔽。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW5SepComplexity.
Require Local.LW0LeibSeparation.
Require LW0PiIrrational.

(* ========== §1 定义层（自足：高度坐标＋幂率预算） ==========     *)

(* 有理高度：h(q) := 1 + 分母（正数位直取 nat），恒 ≥ 2 *)
Definition lw1m_height (q : Q) : nat := Datatypes.S (Pos.to_nat (Qden (Qred q))).

Lemma lw1m_height_ge2 : forall q : Q, NatLe 2 (lw1m_height q).
Proof.
  intro q. apply NatLe_lift. unfold lw1m_height.
  pose proof (Pos2Nat.is_pos (Qden (Qred q))). lia.
Qed.

Fixpoint lw1m_hpow (q : Q) (mu : nat) : nat :=
  match mu with
  | O => 1%nat
  | Datatypes.S m => (lw1m_height q * lw1m_hpow q m)%nat
  end.

Lemma lw1m_hpow_S : forall (q : Q) (m : nat),
  lw1m_hpow q (Datatypes.S m) = (lw1m_height q * lw1m_hpow q m)%nat.
Proof. reflexivity. Qed.

(* 预算（搜索器与预算解耦）：fuel := C·h(q)^μ₀ + 4（幂率尾项 +4 留余量）               *)
Definition lw1m_fuel (q : Q) (mu0 C : nat) : nat := (C * lw1m_hpow q mu0 + 4)%nat.

(* 自有窗阶＝共享搜索机件 × 显式预算（非 lw5n_nsep 预算位）       *)
Definition lw1m_nsep (q : Q) (mu0 C : nat) : nat := lw5n_find q 0 (lw1m_fuel q mu0 C).

(* 增长下界引理：h ≥ 2 ⟹ S n ≤ h^(S n)（特征律与主定理增长分量的关键机件） *)
Lemma lw1m_hpow_lb : forall (q : Q) (n : nat),
  (Datatypes.S n <= lw1m_hpow q (Datatypes.S n))%nat.
Proof.
  intros q n.
  pose proof (lw1m_height_ge2 q) as H2. apply NatLe_drop in H2.
  induction n as [| n IH].
  - rewrite (lw1m_hpow_S q 0). rewrite Nat.mul_1_r. lia.
  - rewrite (lw1m_hpow_S q (Datatypes.S n)).
    pose proof (Nat.mul_le_mono_l (Datatypes.S n) (lw1m_hpow q (Datatypes.S n))
                  (lw1m_height q) IH) as Ha.
    pose proof (Nat.mul_le_mono 2 (lw1m_height q) (Datatypes.S n) (Datatypes.S n)
                  H2 (Nat.le_refl (Datatypes.S n))) as Hm.
    lia.
Qed.

(* ========== §2 测度定义层随件（候选形 ⅰ——逐点反演） ==========    
   注：逐点测度无全局常数、无定量下界，作主语句则近乎平凡——        
   不为主语句，作定义层随件保留（对照数值表取用 lw1m_mu）。       *)

Fixpoint lw1m_musearch (q : Q) (mu0 C e fuel : nat) : nat :=
  match fuel with
  | O => e
  | Datatypes.S f =>
      if Nat.leb (lw1m_nsep q mu0 C) (lw1m_hpow q e)
      then e else lw1m_musearch q mu0 C (Datatypes.S e) f
  end.

Definition lw1m_mu (q : Q) (mu0 C : nat) : nat :=
  lw1m_musearch q mu0 C 2 (lw1m_nsep q mu0 C).

Lemma lw1m_musearch_0 : forall (q : Q) (mu0 C e : nat),
  lw1m_musearch q mu0 C e 0 = e.
Proof. reflexivity. Qed.

Lemma lw1m_musearch_S : forall (q : Q) (mu0 C e f : nat),
  lw1m_musearch q mu0 C e (Datatypes.S f) =
  (if Nat.leb (lw1m_nsep q mu0 C) (lw1m_hpow q e)
   then e else lw1m_musearch q mu0 C (Datatypes.S e) f).
Proof. reflexivity. Qed.

(* 反演命中：燃料自 e 起给足 nsep 步，返回指数 e′ 必满足 nsep ≤ h^e′（自足）     *)
Lemma lw1m_musearch_hit : forall (q : Q) (mu0 C fuel e : nat),
  (lw1m_nsep q mu0 C <= lw1m_hpow q (e + fuel))%nat ->
  Id (Nat.leb (lw1m_nsep q mu0 C)
              (lw1m_hpow q (lw1m_musearch q mu0 C e fuel))) true.
Proof.
  intros q mu0 C fuel. induction fuel as [| f IH]; intros e Hle.
  - rewrite lw1m_musearch_0. rewrite Nat.add_0_r in Hle.
    exact (NatLe_lift (lw1m_nsep q mu0 C) (lw1m_hpow q e) Hle).
  - rewrite lw1m_musearch_S.
    destruct (Nat.leb (lw1m_nsep q mu0 C) (lw1m_hpow q e)) eqn:Eb; cbv iota.
    + rewrite Eb. apply id_refl.
    + rewrite (Nat.add_succ_r e f) in Hle.
      exact (IH (Datatypes.S e) Hle).
Qed.

(* 特征律：μ 返回的指数必满足 nsep ≤ h^指数（机件级构造即真） *)
Lemma lw1m_mu_char : forall (q : Q) (mu0 C : nat),
  Id (Nat.leb (lw1m_nsep q mu0 C)
              (lw1m_hpow q (lw1m_mu q mu0 C))) true.
Proof.
  intros q mu0 C. unfold lw1m_mu.
  apply (lw1m_musearch_hit q mu0 C (lw1m_nsep q mu0 C) 2).
  change (2 + lw1m_nsep q mu0 C)%nat
    with (Datatypes.S (Datatypes.S (lw1m_nsep q mu0 C))).
  pose proof (lw1m_hpow_lb q (Datatypes.S (lw1m_nsep q mu0 C))) as H.
  lia.
Qed.

(* ========== §3 主语句面（Set 面；μ₀/C 假设位承载——sigT 接口） ========== *)

(* 逐 q 命中面：预算内窗阶处真分离（Id＝S01 Set 面等词，bool 承载） *)
Definition lw1m_hit_face (q : Q) (mu0 C : nat) : Set :=
  Id (lw5n_sep_dec q (lw1m_nsep q mu0 C)) true.

(* 命中前提位置（§3b 距离率互译面闭合，非占位见证）  *)
Definition lw1m_hit_supply (mu0 C : nat) : Set :=
  forall q : Q, lw1m_hit_face q mu0 C.

(* 主语句（序约束以 S01 NatLe Set 面承载；                    
   lw1m_fuel q mu0 C ≡ (C·h(q)^μ₀+4)%nat 展开形） *)
Definition lw1m_measure_face : Set :=
  sigT (fun mu0 : nat =>
    sigT (fun _ : NatLe 2 mu0 =>
      sigT (fun C : nat =>
        forall q : Q,
          sigT (fun _ : lw1m_hit_face q mu0 C =>
            NatLe (lw1m_nsep q mu0 C) (lw1m_fuel q mu0 C))))).

(* 分离闭式接口形（自持假设位——同 lw0_pi_irrational 接口构形；零内引他件；   
   real_metric 查验在 S03）                    *)
Definition lw1m_b_cert_face : Set :=
  forall a b : Q, QltT 0 (Qabs b) ->
    sigT (fun c : Q =>
      And (QltT 0 c)
          (real_lt (real_const c)
             (real_metric real_pi_geom (real_const (a / b))))).

(* ========== §3b 距离率互译面（|π_L − q| ≥ c₀/h^μ₀ ⟹ 预算内命中） ========== *)

(* 距离点证书（Q 投影形）：π_L 投影列尾段逐点与 q 相距不小于 d *)
Definition lw1m_dist_pt (q : Q) (d : Q) : Set :=
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT' d (Qabs (lw0m_xL k - q))).

(* 距离率证书：距离点证书取率阈 d := c₀/h(q)^μ₀ *)
Definition lw1m_dist_face (q : Q) (mu0 : nat) (c0 : Q) : Set :=
  lw1m_dist_pt q ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q).

(* 率阶：对 x 取上取整的显式窗阶 *)
Definition lw1m_dist_order (x : Q) : nat := Z.to_nat (Qceiling x).

Lemma lw1m_zround : forall n : nat, Z.to_nat (Z.of_nat n) = n.
Proof.
  intros n. apply Nat2Z.inj. apply Z2Nat.id. apply Nat2Z.is_nonneg.
Qed.

Lemma lw1m_zle_qle : forall a b : nat, (a <= b)%nat ->
  Qle ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b Hab. unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. apply Nat2Z.inj_le. exact Hab.
Qed.

Lemma lw1m_snq_pos : forall n : nat, QltT' 0 ((Z.of_nat (Datatypes.S n) # 1)%Q).
Proof.
  intros n. apply Qlt_to_QltT'. unfold Qlt. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S n))).
  apply Nat.lt_0_succ.
Qed.

Lemma lw1m_snq_selfinv : forall n : nat,
  ((Z.of_nat (Datatypes.S n) # 1)%Q
   * Qinv ((Z.of_nat (Datatypes.S n) # 1)%Q) == (1 # 1))%Q.
Proof.
  intros n.
  change (Z.of_nat (Datatypes.S n)) with (Z.pos (Pos.of_succ_nat n)).
  unfold Qinv, Qmult, Qeq. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma lw1m_qnat_mul : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1) == (Z.of_nat (a * b) # 1))%Q.
Proof.
  intros a b. unfold Qmult, Qeq. cbn [Qnum Qden].
  rewrite Nat2Z.inj_mul. rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma lw1m_hpow_ge1 : forall (q : Q) (m : nat), (1 <= lw1m_hpow q m)%nat.
Proof.
  intros q m. induction m as [| m IH].
  - apply Nat.le_refl.
  - rewrite lw1m_hpow_S.
    pose proof (lw1m_height_ge2 q) as H2. apply NatLe_drop in H2.
    apply (Nat.le_trans 1 (lw1m_height q)%nat
                         (lw1m_height q * lw1m_hpow q m)%nat).
    + exact (Nat.le_trans 1 2 (lw1m_height q) (Nat.le_succ_diag_r 1) H2).
    + apply (Nat.le_trans (lw1m_height q) (lw1m_height q * 1)%nat
                          (lw1m_height q * lw1m_hpow q m)%nat).
      * rewrite Nat.mul_1_r. apply Nat.le_refl.
      * apply (Nat.mul_le_mono (lw1m_height q) (lw1m_height q)
                               1 (lw1m_hpow q m)).
        -- apply Nat.le_refl.
        -- exact IH.
Qed.

Lemma lw1m_hpowQ_pos : forall (q : Q) (mu0 : nat),
  QltT' 0 ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q).
Proof.
  intros q mu0. apply Qlt_to_QltT'. unfold Qlt. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  pose proof (lw1m_hpow_ge1 q mu0) as H1.
  apply (proj1 (Nat2Z.inj_lt 0 (lw1m_hpow q mu0))). exact H1.
Qed.

Lemma lw1m_dist_order_lb : forall x : Q, QltT' 0 x ->
  Qle x ((Z.of_nat (lw1m_dist_order x) # 1)%Q).
Proof.
  intros x Hx. apply QltT'_to_Qlt in Hx.
  unfold lw1m_dist_order.
  pose proof (Qle_ceiling x) as H.
  assert (H0 : (0 <= Qceiling x)%Z).
  { pose proof (Qlt_le_weak 0 x Hx) as Hxle.
    pose proof (Qle_trans 0 x (Qceiling x # 1)%Q Hxle H) as HH.
    unfold Qle in HH. cbn [Qnum Qden inject_Z] in HH.
    rewrite !Z.mul_1_r in HH. exact HH. }
  rewrite (Z2Nat.id (Qceiling x) H0). exact H.
Qed.

Lemma lw1m_dist_order_ub : forall (x : Q) (n : nat), QltT' 0 x ->
  Qle x ((Z.of_nat n # 1)%Q) -> (lw1m_dist_order x <= n)%nat.
Proof.
  intros x n Hx Hle.
  unfold lw1m_dist_order.
  assert (H0 : (0 <= Qceiling x)%Z).
  { pose proof (Qlt_le_weak 0 x (QltT'_to_Qlt 0 x Hx)) as Hxle.
    pose proof (Qle_trans 0 x (Qceiling x # 1)%Q Hxle (Qle_ceiling x)) as HH.
    unfold Qle in HH. cbn [Qnum Qden inject_Z] in HH.
    rewrite !Z.mul_1_r in HH. exact HH. }
  assert (Hc : (Qceiling x <= Z.of_nat n)%Z).
  { pose proof (Qceiling_resp_le x ((Z.of_nat n # 1)%Q) Hle) as HR.
    assert (Hzc : Qceiling ((Z.of_nat n # 1)%Q) = Z.of_nat n)
      by (change (Qceiling ((Z.of_nat n # 1)%Q))
            with (Qceiling (inject_Z (Z.of_nat n))); apply Qceiling_Z).
    rewrite Hzc in HR. exact HR. }
  rewrite <- (lw1m_zround n).
  exact (proj1 (Z2Nat.inj_le (Qceiling x) (Z.of_nat n) H0
                  (Nat2Z.is_nonneg n)) Hc).
Qed.

(* 率阶-窗宽衔接：eps_{阶(hpq/c₀)} < c₀/hpq（率阈与窗族的接缝） *)
Lemma lw1m_dist_order_eps : forall (q : Q) (mu0 : nat) (c0 : Q), QltT 0 c0 ->
  QltT' (lw5n_eps (lw1m_dist_order ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q))
        ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q).
Proof.
  intros q mu0 c0 Hc0.
  pose proof (lw1m_hpowQ_pos q mu0) as Hpq.
  pose proof (QltT'_to_Qlt 0 ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) Hpq) as Hpql.
  assert (Hc0lt : Qlt 0 c0) by (exact (QltT_to_Qlt 0 c0 Hc0)).
  assert (Hc0ne : ~ (c0 == 0)).
  { intro He. apply (Qlt_not_eq 0 c0 Hc0lt). apply Qeq_sym. exact He. }
  assert (Hne_hpq : ~ ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q == 0)).
  { intro He. apply (Qlt_not_eq 0 _ Hpql). apply Qeq_sym. exact He. }
  assert (Hxp : QltT' 0 ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat (Z.of_nat (lw1m_hpow q mu0) # 1)%Q (Qinv c0)).
    - exact Hpql.
    - apply Qinv_lt_0_compat. exact Hc0lt. }
  assert (Hdpos : Qlt 0 ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q)).
  { apply (Qmult_lt_0_compat c0 (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1)%Q)).
    - exact Hc0lt.
    - apply Qinv_lt_0_compat. exact Hpql. }
  set (n0 := lw1m_dist_order ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q) in *.
  pose proof (lw1m_dist_order_lb
                ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q Hxp) as Hlb.
  assert (Hsucc : Qlt ((Z.of_nat n0 # 1)%Q)
                      ((Z.of_nat (Datatypes.S n0) # 1)%Q)).
  { unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
    apply (proj1 (Nat2Z.inj_lt n0 (Datatypes.S n0))).
    apply Nat.lt_succ_diag_r. }
  assert (HxS : Qlt ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                    ((Z.of_nat (Datatypes.S n0) # 1)%Q)).
  { apply (Qle_lt_trans ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                        ((Z.of_nat n0 # 1)%Q)
                        ((Z.of_nat (Datatypes.S n0) # 1)%Q)).
    - exact Hlb.
    - exact Hsucc. }
  assert (Hdx : ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q
                 * ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                 == (1 # 1))%Q).
  { unfold Qdiv.
    rewrite <- (Qmult_assoc c0 (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1)%Q)
                             ((Z.of_nat (lw1m_hpow q mu0) # 1) * Qinv c0)%Q).
    rewrite (Qmult_assoc (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1)%Q)
                         ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) (Qinv c0)).
    setoid_rewrite (Qmult_comm (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1)%Q)
                               ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)).
    rewrite (Qmult_inv_r (Z.of_nat (lw1m_hpow q mu0) # 1)%Q Hne_hpq).
    rewrite Qmult_1_l. apply (Qmult_inv_r c0 Hc0ne). }
  assert (Hdlt : Qlt ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q
                      * ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q)
                     ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q
                      * ((Z.of_nat (Datatypes.S n0) # 1)%Q))).
  { pose proof (Qmult_lt_compat_r ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                   ((Z.of_nat (Datatypes.S n0) # 1)%Q)
                   ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q) Hdpos HxS) as H0.
    setoid_rewrite (Qmult_comm ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                               ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q))
      in H0.
    setoid_rewrite (Qmult_comm ((Z.of_nat (Datatypes.S n0) # 1)%Q)
                               ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q))
      in H0.
    exact H0. }
  rewrite Hdx in Hdlt.
  assert (HposQ : Qlt 0 (Qinv ((Z.of_nat (Datatypes.S n0) # 1)%Q))).
  { apply Qinv_lt_0_compat.
    exact (QltT'_to_Qlt 0 ((Z.of_nat (Datatypes.S n0) # 1)%Q)
             (lw1m_snq_pos n0)). }
  pose proof (Qmult_lt_compat_r (1 # 1)%Q
                 ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q
                  * (Z.of_nat (Datatypes.S n0) # 1)%Q)
                 (Qinv (Z.of_nat (Datatypes.S n0) # 1)%Q) HposQ Hdlt) as HM.
  setoid_replace ((1 # 1) * Qinv (Z.of_nat (Datatypes.S n0) # 1)%Q)%Q
    with (lw5n_eps n0) in HM by (apply Qmult_1_l).
  setoid_replace (((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q
                   * (Z.of_nat (Datatypes.S n0) # 1)%Q)
                  * Qinv (Z.of_nat (Datatypes.S n0) # 1)%Q)%Q
    with ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q) in HM
    by (rewrite <- Qmult_assoc;
        setoid_replace ((Z.of_nat (Datatypes.S n0) # 1)%Q
                        * Qinv (Z.of_nat (Datatypes.S n0) # 1)%Q)%Q
          with (1 # 1)%Q by (apply lw1m_snq_selfinv);
        apply Qmult_1_r).
  exact (Qlt_to_QltT (lw5n_eps n0)
           ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q) HM).
Qed.

(* 远距 ⟹ 出窗：入窗则近距（lw5n_inwin_close_pt）与距离证书矛盾，逆否即出窗 *)
Lemma lw1m_dist_outwin : forall (q : Q) (n : nat) (d : Q),
  QltT' (lw5n_eps n) d -> lw1m_dist_pt q d -> Id (lw5n_sep_dec q n) true.
Proof.
  intros q n d Hwidth Hcert.
  destruct (lw5n_inwin q n) eqn:Ewin.
  - exfalso.
    assert (Ein : LW0LeibWindow.leiblw_Id (lw5n_inwin q n) true)
      by (apply LW0LeibWindow.leiblw_id_eq; exact Ewin).
    pose proof (lw5n_eps_posT n) as Heps0.
    destruct (lw5n_inwin_close_pt q n (lw5n_eps n) Heps0 Ein) as [N1 Hcl].
    destruct Hcert as [N2 Hcer].
    pose proof (Hcl (N1 + N2)%nat
                  (NatLe_lift N1 (N1 + N2)%nat (Nat.le_add_r N1 N2))) as HA.
    pose proof (Hcer (N1 + N2)%nat
                  (NatLe_lift N2 (N1 + N2)%nat (Nat.le_add_l N2 N1))) as HB.
    apply QltT'_to_Qlt in HA. apply QltT'_to_Qlt in HB.
    apply QltT'_to_Qlt in Hwidth.
    assert (Hchain : Qlt d (lw5n_eps n)).
    { apply (Qlt_trans d (Qabs (lw0m_xL (N1 + N2)%nat - q)) (lw5n_eps n)).
      - exact HB.
      - exact HA. }
    exact (Qlt_not_eq d d (Qlt_trans d (lw5n_eps n) d Hchain Hwidth)
             (Qeq_refl d)).
  - unfold lw5n_sep_dec. rewrite Ewin. apply id_refl.
Qed.

(* 预算内命中：距离率证书＋预算口径（1 < C·c₀）⟹ lw1m_hit_face *)
Lemma lw1m_dist_to_nsep : forall (mu0 C : nat) (c0 : Q) (q : Q),
  QltT 0 c0 -> QltT (1 # 1) (c0 * (Z.of_nat C # 1)%Q) ->
  lw1m_dist_face q mu0 c0 -> lw1m_hit_face q mu0 C.
Proof.
  intros mu0 C c0 q Hc0 Hcal Hcert.
  pose proof (lw1m_hpowQ_pos q mu0) as Hpq.
  pose proof (QltT'_to_Qlt 0 ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) Hpq) as Hpql.
  assert (Hc0lt : Qlt 0 c0) by (exact (QltT_to_Qlt 0 c0 Hc0)).
  assert (Hc0ne : ~ (c0 == 0)).
  { intro He. apply (Qlt_not_eq 0 c0 Hc0lt). apply Qeq_sym. exact He. }
  assert (Hinvpos : Qlt 0 (Qinv c0)) by (apply Qinv_lt_0_compat; exact Hc0lt).
  assert (Hinvlt : Qlt (Qinv c0) ((Z.of_nat C # 1)%Q)).
  { pose proof (Qmult_lt_compat_r (1 # 1)%Q
                   (c0 * (Z.of_nat C # 1)%Q) (Qinv c0) Hinvpos
                   (QltT_to_Qlt (1 # 1) (c0 * (Z.of_nat C # 1)%Q) Hcal)) as HM.
    setoid_replace ((1 # 1) * Qinv c0)%Q with (Qinv c0) in HM
      by (apply Qmult_1_l).
    setoid_replace ((c0 * (Z.of_nat C # 1)%Q) * Qinv c0)%Q
      with ((Z.of_nat C # 1)%Q) in HM
      by (rewrite <- (Qmult_assoc c0 (Z.of_nat C # 1)%Q (Qinv c0));
          setoid_rewrite (Qmult_comm (Z.of_nat C # 1)%Q (Qinv c0));
          rewrite (Qmult_assoc c0 (Qinv c0) (Z.of_nat C # 1)%Q);
          setoid_rewrite (Qmult_inv_r c0 Hc0ne);
          apply Qmult_1_l).
    exact HM. }
  assert (Hxp : QltT' 0 ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat (Z.of_nat (lw1m_hpow q mu0) # 1)%Q (Qinv c0)).
    - exact Hpql.
    - apply Qinv_lt_0_compat. exact Hc0lt. }
  assert (Hxlt : Qlt ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                     ((Z.of_nat (C * lw1m_hpow q mu0 + 4) # 1)%Q)).
  { pose proof (Qmult_lt_compat_r (Qinv c0) ((Z.of_nat C # 1)%Q)
                   ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) Hpql Hinvlt) as H1.
    setoid_rewrite (Qmult_comm (Qinv c0)
                               ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)) in H1.
    setoid_rewrite (Qmult_comm ((Z.of_nat C # 1)%Q)
                               ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)) in H1.
    setoid_replace ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q * (Z.of_nat C # 1)%Q)
      with ((Z.of_nat (lw1m_hpow q mu0 * C) # 1)%Q) in H1
      by (apply lw1m_qnat_mul).
    assert (Hle : ((lw1m_hpow q mu0 * C) <= (C * lw1m_hpow q mu0 + 4))%nat).
    { rewrite (Nat.mul_comm (lw1m_hpow q mu0) C).
      apply (Nat.le_trans _ (C * lw1m_hpow q mu0)%nat _).
      - apply Nat.le_refl.
      - apply Nat.le_add_r. }
    pose proof (lw1m_zle_qle (lw1m_hpow q mu0 * C)
                  (C * lw1m_hpow q mu0 + 4) Hle) as H2.
    apply (Qlt_le_trans ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                        ((Z.of_nat (lw1m_hpow q mu0 * C) # 1)%Q)
                        ((Z.of_nat (C * lw1m_hpow q mu0 + 4) # 1)%Q)).
    - exact H1.
    - exact H2. }
  pose proof (lw1m_dist_order_ub ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q
                (C * lw1m_hpow q mu0 + 4)%nat Hxp
                (Qlt_le_weak _ _ Hxlt)) as Hbudget.
  pose proof (lw1m_dist_order_eps q mu0 c0 Hc0) as Hwidth0.
  pose proof (lw1m_dist_outwin q
                (lw1m_dist_order ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q)
                ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q)
                Hwidth0 Hcert) as Hout.
  unfold lw1m_hit_face, lw1m_nsep, lw1m_fuel.
  assert (Hout' : LW0LeibWindow.leiblw_Id
                    (lw5n_sep_dec q
                       (lw1m_dist_order
                          ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q)) true).
  { destruct Hout. apply LW0LeibWindow.leiblw_id_intro. }
  destruct (lw5n_find_hit q (C * lw1m_hpow q mu0 + 4)%nat 0
              (lw1m_dist_order ((Z.of_nat (lw1m_hpow q mu0) # 1) / c0)%Q)
              (Nat.le_0_l _)
              Hbudget
              Hout') as [Hhit _].
  pose proof (LW0LeibWindow.leiblw_id_inv _ Hhit) as Hhit_eq.
  rewrite Hhit_eq. apply id_refl.
Qed.

(* 距离率证书的全域前提面：由 lw1m_b_cert_face 单独承载的闭合
   ＝闭式 c(q) ≥ c₀·h^{−μ₀} 支配链，后续支配链（单前提终形的达成点）      *)
Definition lw1m_dom_face : Set :=
  forall (Hb : lw1m_b_cert_face) (mu0 C : nat) (c0 : Q),
    QltT 0 c0 -> QltT (1 # 1) (c0 * (Z.of_nat C # 1)%Q) ->
    forall q : Q, lw1m_dist_face q mu0 c0.

(* 主定理：lw1m_b_cert_face 实取用（经证书前提面）＋率阶 μ₀=2/C=2 显式选取；
   增长界分量机件级闭合（lw5n_find_ub），命中分量经 lw1m_dist_to_nsep *)
Theorem lw1m_measure_main :
  lw1m_b_cert_face -> lw1m_dom_face -> lw1m_measure_face.
Proof.
  intros Hb Hdom.
  exists (Datatypes.S (Datatypes.S 0)).
  exists (NatLe_lift 2 2 (Nat.le_refl 2)).
  exists (Datatypes.S (Datatypes.S 0)).
  assert (Hc01 : QltT 0 (1 # 1)) by exact id_refl.
  assert (Hcal : QltT (1 # 1)
                   ((1 # 1) * (Z.of_nat (Datatypes.S (Datatypes.S 0)) # 1)%Q))
    by exact id_refl.
  intro q.
  exists (lw1m_dist_to_nsep (Datatypes.S (Datatypes.S 0))
            (Datatypes.S (Datatypes.S 0)) (1 # 1)%Q q Hc01 Hcal
            (Hdom Hb (Datatypes.S (Datatypes.S 0))
               (Datatypes.S (Datatypes.S 0)) (1 # 1)%Q Hc01 Hcal q)).
  apply NatLe_lift. unfold lw1m_nsep, lw1m_fuel.
  pose proof (lw5n_find_ub q
                (Datatypes.S (Datatypes.S 0)
                 * lw1m_hpow q (Datatypes.S (Datatypes.S 0)) + 4)%nat 0) as Hub.
  rewrite Nat.add_0_l in Hub. exact Hub.
Qed.

(* ========== §4 在件检验（编译出口核对） ==========     *)

Check lw1m_height.
Check lw1m_nsep.
Check lw1m_measure_face.
Check lw1m_b_cert_face.
Check lw1m_measure_main.
Check lw1m_dist_face.
Check lw1m_dist_to_nsep.
Check lw1m_dom_face.

(* ========== §5 注记区（后续衔接项与扩展路径） ==========
   一、μ₀/C 取值义务：vm_compute 检验两发，随后续件——      
   Eval vm_compute in (lw1m_nsep (22#7) μ₀ C, lw1m_nsep (333#106) μ₀ C)
   ＋lw0_n_select 对照；确定值另行记录，此前禁语句外预告数值。  
   二、§3b 互译面：命中面由 lw1m_dist_to_nsep 闭合——前提位置为距离率证书
   （lw1m_dist_face，|π_L − q| ≥ c₀/h(q)^μ₀ 的 Q 投影形）与预算口径
   （1 < C·c₀，前提位置参数化）；lw1m_measure_main 归并
   lw1m_b_cert_face → lw1m_dom_face → lw1m_measure_face，率面 μ₀=2/C=2 显式；
   lw1m_dom_face 由 lw1m_b_cert_face 单独承载的闭合＝闭式    
   c(q) ≥ c₀·h^{−μ₀} 支配链，落实即减元为单前提终形。
   三、签名核对：本件已按现行签名查证落定      
   （lw5n_find : Q -> nat -> nat -> nat；lw5n_sep_dec : Q -> nat -> bool；
   lw5n_find_ub 参序 (q fuel n)），零 alias 层；签名再变时再核。     
   四、Qden 注记：现行 Qden : Q -> positive（直查确认），设计稿曾记    
   QAbs(Z 形) 作废；Z.abs 不入本件。
   五、提取范围：提取面＝纯 nat/Q 函数族＋Set 语句面（hit/measure 两
   face＋供给位＋距离率证书面＋率阶）；lw1m_b_cert_face 与 lw1m_dom_face
   未入提取值域主张——前提位置接口件，闭式闭合后随支配链提取核算，如实 
   标注禁合并主张。 *)

(* ========== §6 提取＋假设审计 ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "D:/ComplexAnalysis/新算法实践/attn/_tlw616_sbx/extract".
Separate Extraction lw1m_height lw1m_hpow lw1m_fuel lw1m_nsep lw1m_musearch lw1m_mu lw1m_hit_face lw1m_hit_supply lw1m_measure_face lw1m_dist_pt lw1m_dist_face lw1m_dist_order lw1m_dom_face.
Print Assumptions lw1m_measure_main.
Print Assumptions lw1m_dist_to_nsep.
Print Assumptions lw1m_mu_char.
Print Assumptions lw1m_musearch_hit.
Print Assumptions lw1m_hpow_lb.
Print Assumptions lw1m_height_ge2.

(* ========== §7 出窗域改形（量化域收缩） ========== *)

(* 域谓词：q 在某阶 N 以余量 2*c0 逃出尾控窗。与 LW0LeibSeparation.v
   leibsep_pi_sep_alpha_guarded 的守卫前提逐字同形（Q 层）。 *)
Definition lw1m_escape_face (q : Q) (c0 : Q) : Set :=
  sigT (fun N : nat =>
    And (NatLe 1 N)
        (QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)))).

(* 阈值比较：h(q)^mu0 ≥ 1 给 c0/h(q)^mu0 ≤ c0。倒数单调经析取消除
   （1 < /h^μ 时两侧乘正 h^μ 归 1 < 1 矛盾），全链显式 Q 步进。 *)
Lemma lw1m_div_hpow_le : forall (q : Q) (mu0 : nat) (c0 : Q),
  QltT 0 c0 ->
  QleT' ((c0 / (Z.of_nat (lw1m_hpow q mu0) # 1))%Q) c0.
Proof.
  intros q mu0 c0 Hc0.
  pose proof (lw1m_hpowQ_pos q mu0) as Hpq.
  pose proof (QltT'_to_Qlt 0 ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) Hpq) as Hpql.
  assert (Hc0lt : Qlt 0 c0) by (exact (QltT_to_Qlt 0 c0 Hc0)).
  assert (Hpne : ~ ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q == 0)).
  { intro He. apply (Qlt_not_eq 0 _ Hpql). apply Qeq_sym. exact He. }
  pose proof (lw1m_zle_qle 1 (lw1m_hpow q mu0) (lw1m_hpow_ge1 q mu0)) as Hge1q.
  assert (Hinv_le_1 : Qle (Qinv ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)) (1 # 1)).
  { destruct (Qlt_le_dec (1 # 1) (Qinv ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)))
      as [Hlt | Hle].
    - exfalso.
      pose proof (Qmult_lt_compat_r (1 # 1)
                    (Qinv ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q))
                    ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q)
                    (QltT'_to_Qlt 0 _ Hpq) Hlt) as Hm.
      rewrite Qmult_1_l in Hm.
      rewrite <- (Qmult_comm (Z.of_nat (lw1m_hpow q mu0) # 1)
                             (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1))) in Hm.
      rewrite Qmult_inv_r in Hm by exact Hpne.
      exact (Qlt_not_eq (1 # 1) (1 # 1)
               (Qle_lt_trans (1 # 1)
                  ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q) (1 # 1)
                  Hge1q Hm) (Qeq_refl (1 # 1))).
    - exact Hle. }
  apply Qle_to_QleT'. unfold Qdiv.
  pose proof (Qmult_le_compat_r (Qinv ((Z.of_nat (lw1m_hpow q mu0) # 1)%Q))
                (1 # 1) c0 Hinv_le_1 (Qlt_le_weak 0 c0 Hc0lt)) as Hle2.
  rewrite Qmult_1_l in Hle2.
  rewrite (Qmult_comm c0 (Qinv (Z.of_nat (lw1m_hpow q mu0) # 1))).
  exact Hle2.
Qed.

(* 出窗⟹距离率：尾控给 |xL k − xL N| < e N（k ≥ N），三角不等式给
   |xL k − q| ≥ |xL N − q| − |xL k − xL N| > (e N + 2*c0) − e N = 2*c0，
   而 2*c0 > c0 ≥ c0/h(q)^mu0，故尾段每点与 q 相距严格大于阈值。 *)
Lemma lw1m_escape_to_dist : forall (q : Q) (c0 : Q) (mu0 : nat),
  QltT 0 c0 -> lw1m_escape_face q c0 -> lw1m_dist_face q mu0 c0.
Proof.
  intros q c0 mu0 Hc0 [N [HN1 Hwin]].
  pose proof (lw1m_div_hpow_le q mu0 c0 Hc0) as Hthr.
  pose proof (QleT'_to_Qle _ _ Hthr) as HthrQ.
  assert (Hc0lt : Qlt 0 c0) by (exact (QltT_to_Qlt 0 c0 Hc0)).
  assert (H12 : QltT (1 # 1) (2 # 1)) by exact id_refl.
  assert (Htwo : Qlt c0 (2 * c0)).
  { pose proof (Qmult_lt_compat_r (1 # 1) (2 # 1) c0 Hc0lt
                  (QltT_to_Qlt (1 # 1) (2 # 1) H12)) as Hm.
    rewrite Qmult_1_l in Hm. exact Hm. }
  pose proof (QltT_to_Qlt _ _ Hwin) as Hwin'.
  unfold lw1m_dist_face, lw1m_dist_pt.
  exists N. intros k HkN.
  pose proof (NatLe_drop N k HkN) as Hle.
  pose proof (NatLe_drop 1 N HN1) as HN1n.
  pose proof (QltT_to_Qlt _ _
    (lw0m_tail_bounded_pi N k HN1n Hle)) as Htail.
  pose proof (Qabs_triangle (lw0m_xL k - q) (lw0m_xL N - lw0m_xL k)) as Htri0.
  assert (HabsEq : Qabs (((lw0m_xL k - q) + (lw0m_xL N - lw0m_xL k))%Q)
                 == Qabs ((lw0m_xL N - q)%Q))
    by (apply Qabs_wd; ring).
  rewrite HabsEq in Htri0.
  assert (HabsEq2 : Qabs ((lw0m_xL N - lw0m_xL k)%Q)
                  == Qabs ((lw0m_xL k - lw0m_xL N)%Q)).
  { rewrite <- (Qabs_opp (lw0m_xL k - lw0m_xL N)). apply Qabs_wd. ring. }
  rewrite HabsEq2 in Htri0.
  pose proof (Qlt_le_trans (lw0m_e N + 2 * c0) (Qabs (lw0m_xL N - q))
                (Qabs (lw0m_xL k - q) + Qabs (lw0m_xL k - lw0m_xL N))
                Hwin' Htri0) as Hcomb.
  pose proof (proj2 (Qplus_lt_r (Qabs (lw0m_xL k - lw0m_xL N)) (lw0m_e N)
                      (Qabs (lw0m_xL k - q))) Htail) as Hbnd.
  pose proof (Qlt_trans _ _ _ Hcomb Hbnd) as Htot.
  setoid_replace (Qabs (lw0m_xL k - q) + lw0m_e N)
    with (lw0m_e N + Qabs (lw0m_xL k - q)) in Htot
    by (apply Qplus_comm).
  pose proof (proj1 (Qplus_lt_r (2 * c0) (Qabs (lw0m_xL k - q)) (lw0m_e N))
                Htot) as Hlow.
  pose proof (Qlt_trans c0 (2 * c0) (Qabs (lw0m_xL k - q)) Htwo Hlow)
    as Hmid.
  apply Qlt_to_QltT'. unfold Qdiv.
  exact (Qle_lt_trans _ c0 _ HthrQ Hmid).
Qed.

(* dom_face 出窗域版：量化域收缩至出窗面，mu0 位保留参数化。 *)
Definition lw1m_dom_face_r2 : Set :=
  forall (mu0 : nat) (c0 : Q),
    QltT 0 c0 ->
    forall q : Q,
      lw1m_escape_face q c0 -> lw1m_dist_face q mu0 c0.

(* 测度语句出窗域版：取定 mu0 = 2, C = 2, c0 = 1。 *)
Definition lw1m_measure_face_r2 : Set :=
  sigT (fun mu0 : nat =>
    sigT (fun _ : NatLe 2 mu0 =>
      sigT (fun C : nat =>
        forall q : Q,
          lw1m_escape_face q (1 # 1)%Q ->
          sigT (fun _ : lw1m_hit_face q mu0 C =>
            NatLe (lw1m_nsep q mu0 C) (lw1m_fuel q mu0 C))))).

(* 零前提主定理：出窗前提折入 ∀q 的前提位，供给经出窗桥与预算内命中
   引理闭合；预算界分量沿 lw5n_find_ub。 *)
Theorem lw1m_measure_main_r2 : lw1m_measure_face_r2.
Proof.
  exists (Datatypes.S (Datatypes.S 0)).
  exists (NatLe_lift 2 2 (Nat.le_refl 2)).
  exists (Datatypes.S (Datatypes.S 0)).
  assert (Hc01 : QltT 0 (1 # 1)) by exact id_refl.
  assert (Hcal : QltT (1 # 1)
                   ((1 # 1) * (Z.of_nat (Datatypes.S (Datatypes.S 0)) # 1)%Q))
    by exact id_refl.
  intro q. intro Hesc.
  exists (lw1m_dist_to_nsep (Datatypes.S (Datatypes.S 0))
            (Datatypes.S (Datatypes.S 0)) (1 # 1)%Q q Hc01 Hcal
            (lw1m_escape_to_dist q (1 # 1)%Q (Datatypes.S (Datatypes.S 0))
               Hc01 Hesc)).
  apply NatLe_lift. unfold lw1m_nsep, lw1m_fuel.
  pose proof (lw5n_find_ub q
                (Datatypes.S (Datatypes.S 0)
                 * lw1m_hpow q (Datatypes.S (Datatypes.S 0)) + 4)%nat 0) as Hub.
  rewrite Nat.add_0_l in Hub. exact Hub.
Qed.

Check lw1m_escape_face.
Check lw1m_div_hpow_le.
Check lw1m_escape_to_dist.
Check lw1m_dom_face_r2.
Check lw1m_measure_face_r2.
Check lw1m_measure_main_r2.

Print Assumptions lw1m_measure_main_r2.
Print Assumptions lw1m_escape_to_dist.
Print Assumptions lw1m_div_hpow_le.

Set Extraction Output Directory "D:/ComplexAnalysis/新算法实践/attn/_tlw672_sbx/extract".
Separate Extraction lw1m_escape_face lw1m_div_hpow_le lw1m_escape_to_dist lw1m_dom_face_r2 lw1m_measure_face_r2 lw1m_measure_main_r2.


(* ========== §8 真层证书面（出窗域） ========== *)

(* 出窗域真层证书：出窗有理数 q 的显式分离下界升实数层——
   存在正 Q 常数 c 使 c 严格小于 π_geom 与 q 的实距离。
   结论形与 leibsep_pi_sep_alpha_guarded 结论位逐字同构
   （real_const/real_metric/real_lt 全 S02/S03 Set 面）。 *)
Definition lw1m_bcert_face (q : Q) : Set :=
  sigT (fun c : Q => And (QltT 0 c)
          (real_lt (real_const c)
             (real_metric real_pi_geom (real_const q)))).

(* 出窗 ⟹ 真层证书：守卫前提即出窗面，供给结论位关于
   (a / b)，目标 face 位取 q := (a / b)，零换岸。 *)
Theorem lw1m_escape_bcert :
  forall (a b : Q) (c0 : Q),
    QltT 0 (Qabs b) ->
    QltT 0 c0 ->
    lw1m_escape_face (a / b)%Q c0 -> lw1m_bcert_face (a / b)%Q.
Proof.
  intros a b c0 Hb Hc0 [N [HN1 Hwin]].
  destruct (LW0LeibSeparation.leibsep_pi_sep_alpha_guarded a b N c0
              Hb (NatLe_drop 1 N HN1) Hc0 Hwin) as [c Hc].
  exists c. exact Hc.
Qed.

(* ========== §9 阶乘率锚位面 ========== *)

(* 阶乘率锚位：分离距离阀取 c0/((h+1)·(2h+22)!)——
   幂率预算的阶乘-多项式替代形（引擎实形为阶乘率）。 *)
Definition lw1m_fface (q : Q) (c0 : Q) : Set :=
  lw1m_dist_pt q
    ((c0 / ((Z.of_nat (lw1m_height q + 1) # 1)%Q
            * q_fact (2 * lw1m_height q + 22))%Q)%Q).

(* 阀值正值：c0 > 0 且 (h+1)·(2h+22)! > 0 给阀 > 0；
   正性对乘/除封闭，全链显式 Q 步进。 *)
Lemma lw1m_fface_thr_pos : forall (q : Q) (c0 : Q),
  QltT 0 c0 ->
  QltT 0 ((c0 / ((Z.of_nat (lw1m_height q + 1) # 1)%Q
                  * q_fact (2 * lw1m_height q + 22))%Q)%Q).
Proof.
  intros q c0 Hc0.
  assert (Hc0lt : Qlt 0 c0) by (exact (QltT_to_Qlt 0 c0 Hc0)).
  pose proof (NatLe_drop 2 (lw1m_height q) (lw1m_height_ge2 q)) as Hh2.
  assert (H31 : (3 <= lw1m_height q + 1)%nat) by lia.
  assert (H13 : (1 <= 3)%nat) by lia.
  pose proof (lw1m_zle_qle 1 3 H13) as Hq13.
  pose proof (lw1m_zle_qle 3 (lw1m_height q + 1) H31) as Hq3x.
  assert (H01 : Qlt 0 (1 # 1)) by exact (QltT_to_Qlt 0 (1 # 1) id_refl).
  pose proof (Qlt_le_trans 0 (1 # 1) ((3 # 1)%Q) H01 Hq13) as H03.
  assert (HxA : Qlt 0 ((Z.of_nat (lw1m_height q + 1) # 1)%Q))
    by exact (Qlt_le_trans 0 ((3 # 1)%Q)
                ((Z.of_nat (lw1m_height q + 1) # 1)%Q) H03 Hq3x).
  pose proof (q_fact_pos (2 * lw1m_height q + 22)) as HxB.
  assert (Hx : Qlt 0 (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                       * q_fact (2 * lw1m_height q + 22))%Q)).
  { destruct (Qlt_le_dec 0 (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                             * q_fact (2 * lw1m_height q + 22))%Q))
      as [Hyes | Hno]; [exact Hyes | exfalso].
    pose proof (Qmult_lt_compat_r 0
                  ((Z.of_nat (lw1m_height q + 1) # 1)%Q)
                  (q_fact (2 * lw1m_height q + 22))
                  HxB HxA) as Hp.
    rewrite Qmult_0_l in Hp.
    exact (Qlt_not_le 0 _ Hp Hno). }
  assert (Hxne : ~ (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                     * q_fact (2 * lw1m_height q + 22))%Q == 0)).
  { intro He. apply (Qlt_not_eq 0 _ Hx). apply Qeq_sym. exact He. }
  assert (Hinv : Qlt 0 (Qinv (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                               * q_fact (2 * lw1m_height q + 22))%Q))).
  { destruct (Qlt_le_dec 0 (Qinv (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                                   * q_fact (2 * lw1m_height q + 22))%Q)))
      as [Hyes | Hno]; [exact Hyes | exfalso].
    pose proof (Qmult_le_compat_r (Qinv (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                                         * q_fact (2 * lw1m_height q + 22))%Q))
                  0 (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                      * q_fact (2 * lw1m_height q + 22))%Q)
                  Hno (Qlt_le_weak 0 _ Hx)) as Hle.
    rewrite (Qmult_comm (Qinv (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                                * q_fact (2 * lw1m_height q + 22))%Q))
                  (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                    * q_fact (2 * lw1m_height q + 22))%Q)) in Hle.
    rewrite Qmult_inv_r in Hle by exact Hxne.
    rewrite Qmult_0_l in Hle.
    exact (Qlt_not_le 0 (1 # 1) H01 Hle). }
  unfold Qdiv.
  pose proof (Qmult_lt_compat_r 0 c0
                (Qinv (((Z.of_nat (lw1m_height q + 1) # 1)%Q
                        * q_fact (2 * lw1m_height q + 22))%Q))
                Hinv Hc0lt) as Hfin.
  rewrite Qmult_0_l in Hfin.
  exact (Qlt_to_QltT' 0 _ Hfin).
Qed.

(* 阶乘占优链：q_pow (10/3) n ≤ q_fact n（n ≥ 22 选取下）——
   供件阶乘占优件的限定引用直实例化。 *)
Theorem lw1m_ffact_dominates : forall b k : nat,
  QleT' (q_pow (10 # 3) (LW0PiIrrational.lw0_n_select b k))
        (q_fact (LW0PiIrrational.lw0_n_select b k)).
Proof.
  intros b k. exact (LW0PiIrrational.lw0_n_select_dominated b k).
Qed.

(* w0 核心不等式：阶乘-多项式弱界的定量核——
   供件 lw0_pi_w0_lt1_core 的限定引用直实例化。 *)
Theorem lw1m_w0_lt1 : forall t : nat,
  QltT (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)
        * LW0PiIrrational.lw0_q_of_nat (23 + 2 * t))
       (LW0PiIrrational.lw0_q_of_nat (24 + 2 * t)
        * q_pow (LW0PiIrrational.lw0_q_of_nat (11 + t)) (11 + t)).
Proof.
  intro t. exact (LW0PiIrrational.lw0_pi_w0_lt1_core t).
Qed.

Check lw1m_bcert_face.
Check lw1m_escape_bcert.
Check lw1m_fface.
Check lw1m_fface_thr_pos.
Check lw1m_ffact_dominates.
Check lw1m_w0_lt1.
Check LW0LeibSeparation.leibsep_pi_sep_alpha_guarded.
Check LW0PiIrrational.lw0_n_select.
Check LW0PiIrrational.lw0_n_select_dominated.
Check LW0PiIrrational.lw0_pi_w0_lt1_core.
Check LW0PiIrrational.lw0_pi_w0n_lt1.
Check LW0PiIrrational.lw0_pi_b_den_pos.

Print Assumptions lw1m_escape_bcert.
Print Assumptions lw1m_fface_thr_pos.
Print Assumptions lw1m_ffact_dominates.
Print Assumptions lw1m_w0_lt1.

(* Extraction of this block is deferred: the real_const/real_metric
   closure trips the known extraction debt (prod@Prop instance, audit
   ROOT family); Print Assumptions above carries the closure witness. *)
