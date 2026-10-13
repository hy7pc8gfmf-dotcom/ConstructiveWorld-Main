(* ================================================================== *)
(* LeibsepBandDomain —— W1-α'' 带域引理件（带域谓词＋成员核＋阀形接口）   *)
(*                                                                    *)
(* 使命：leibsep_q_kernel 门1 假支带域前提的可形式化最小面。①带域谓词    *)
(*   piu1866_in_band q := 35/12 < q < 41/12（1862 锁死带）；②成员核引理  *)
(*   （GAPASUME·Section Hypothesis 位显式承载）：窗面 Hwin/Hx3/HxL ＋阈  *)
(*   条件 e_N1≤e3∧e_N1≤el∧eps1≤1/3 ⟹ 带域；③链面实例化肢（e_N1 <       *)
(*   eps1/4 ≤ min(eg,el) ∧ eg≤e3 时阈条件自足）；④Qred 归位肢；⑤阀形    *)
(*   接口：valve_R1（WING 坐标·R_W≥1 可容 c0=1 形）与 valve_closed       *)
(*   （闭式坐标）经互译恒等式前提参数位互换；2n_sel+2=40h+48 桥接既有件。*)
(* 依赖：Stdlib QArith/Qabs/Qminmax/ZArith/Lia/Lqa；S01_BaseRing；       *)
(*   S03_QExp（q_fact/q_pow）；LW0PiIrrational（lw0_Wb :1336）；          *)
(*   LW1PiMeasure（lw1m_height :48）；leibsep_nsel_h_coupling（born 件）。 *)
(* 对标行：LW0LeibSeparation :3928（gate_carrier）；:5452（kernel）；     *)
(*   :5509-:5528（eps1 形）；:5551/:5560（vanish 窗）；:5574-:5590（门1   *)
(*   假支窗面·前提位形基准）；:5596/:5609（WING/eps2）；tlw1703_unif     *)
(*   :46-:56（Hypothesis 前提位惯例）。施工图源：PIU1862 §2.3/§5＋        *)
(*   PIU1864 §8 turnkey。                                                *)
(* 构造性注记：全 Set/Prop 层；Section 关闭后假设位转前提位；Qabs 两岸    *)
(*   Qle_Qabs/Qabs_Qminus（Leibniz = 形）；Qred 归位走 Qred_lt；lra 仅 Q  *)
(*   线性算术记录；Qeq 传递微件走 %Z 交叉分子式确定性链（Q_scope 压顶病治）；*)
(*   互译恒等式系 1862 P6 Fraction 双侧已证算术，本件以前提参数位承载     *)
(*   （本闭包 field/ring 实例未注册）。零 Axiom/Admitted。               *)
(* 编译配方：coqc -native-compiler no -q -Q <vo树> "" -Q . "" 本件        *)
(*   （COQLIB/ROCQLIB 字面 export；cpu_guard v3 包裹；runner＝_run1866.py）。 *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Lqa.
Require Import S01_BaseRing.
Require Import S03_QExp.
Require Import LW0PiIrrational.
Require Import LW1PiMeasure.
Require Import leibsep_nsel_h_coupling.

(* ---------- §1 带域谓词（1862 锁死带 35/12 < q < 41/12） ---------- *)

Definition piu1866_band_lo : Q := (35 # 12)%Q.
Definition piu1866_band_hi : Q := (41 # 12)%Q.

Definition piu1866_in_band (q : Q) : Prop :=
  Qlt piu1866_band_lo q /\ Qlt q piu1866_band_hi.

(* ---------- §2 Qabs 两岸微件（Leibniz = 形·零 setoid） ---------- *)

Lemma piu1866_qabs_shores : forall d u : Q,
  Qle (Qabs d) u -> Qle d u /\ Qle (- d) u.
Proof.
  intros d u H. split.
  - exact (Qle_trans d (Qabs d) u (Qle_Qabs d) H).
  - pose proof (Qle_Qabs (- d)) as H2. rewrite Qabs_opp in H2.
    exact (Qle_trans (- d) (Qabs d) u H2 H).
Qed.

(* ---------- §3 成员核引理（GAPASUME·Hypothesis 位显式承载） ---------- *)

Section BandCert.

Variable q xL eN1 eps1 e3 el : Q.
(* 窗面三条＝门1 假支 :5574/:5578/:5581 逐字转录（QleT'/QltT 基座经      *)
(* QleT'_to_Qle/QltT_to_Qle 一次转换后入题·本件取裸 Qle/Qlt 形）。       *)
Hypothesis Hwin : Qle (Qabs ((xL - q)%Q)) (eN1 + 2 * (eps1 * (1 # 8))%Q).
Hypothesis Hx3 : Qlt e3 ((xL - 3)%Q).
Hypothesis HxL : Qlt el ((10 # 3)%Q - xL)%Q.
(* 阈条件两条＝1862 §5 工位画像「补阈条件假设面」之落装：                *)
(*   e_N1≤e3（下界肢）、e_N1≤el（上界肢）。                              *)
Hypothesis HeN1e3 : Qle eN1 e3.
Hypothesis HeN1el : Qle eN1 el.
(* eps1 面＝:5528 Hep1e3。                                              *)
Hypothesis Hep13 : Qle eps1 (1 # 3)%Q.

Lemma piu1866_band_cert : piu1866_in_band q.
Proof.
  unfold piu1866_in_band.
  assert (Hs1 : Qle ((xL - q)%Q) (eN1 + 2 * (eps1 * (1 # 8))%Q))
    by exact (proj1 (piu1866_qabs_shores (xL - q)%Q
              (eN1 + 2 * (eps1 * (1 # 8))%Q) Hwin)).
  assert (Hs2 : Qle ((q - xL)%Q) (eN1 + 2 * (eps1 * (1 # 8))%Q)).
  { pose proof (Qle_Qabs ((q - xL)%Q)) as H2.
    rewrite (Qabs_Qminus q xL) in H2.
    exact (Qle_trans (q - xL)%Q (Qabs ((xL - q)%Q))
             (eN1 + 2 * (eps1 * (1 # 8))%Q) H2 Hwin). }
  split.
  - unfold piu1866_band_lo. lra.
  - unfold piu1866_band_hi. lra.
Qed.

End BandCert.

(* ---------- §4 链面实例化肢（e_N1 < eps1/4 ≤ min(eg,el) 面） ---------- *)

Lemma piu1866_band_kernel_windows :
  forall q xL eN1 eps1 eg el e3 : Q,
    Qle (Qabs ((xL - q)%Q)) (eN1 + 2 * (eps1 * (1 # 8))%Q) ->
    Qlt e3 ((xL - 3)%Q) ->
    Qlt el ((10 # 3)%Q - xL)%Q ->
    Qlt eN1 (eps1 * (1 # 4))%Q ->
    Qle 0 eps1 ->
    Qle eps1 eg ->
    Qle eg e3 ->
    Qle eps1 el ->
    Qle eps1 (1 # 3)%Q ->
    piu1866_in_band q.
Proof.
  intros q xL eN1 eps1 eg el e3 Hwin Hx3 HxL HeN14 Hp0 Hpeg Hge3 Hpel Hep13.
  apply (piu1866_band_cert q xL eN1 eps1 e3 el);
    [ exact Hwin | exact Hx3 | exact HxL | lra | lra | exact Hep13 ].
Qed.

(* ---------- §5 Qred 归位肢（带域谓词 Qred 不变量） ---------- *)

Lemma piu1866_in_band_Qred_iff : forall q : Q,
  piu1866_in_band (Qred q) <-> piu1866_in_band q.
Proof.
  intros q. unfold piu1866_in_band. split; intros [H1 H2]; split.
  - exact (proj1 (Qred_lt piu1866_band_lo q) H1).
  - exact (proj1 (Qred_lt q piu1866_band_hi) H2).
  - exact (proj2 (Qred_lt piu1866_band_lo q) H1).
  - exact (proj2 (Qred_lt q piu1866_band_hi) H2).
Qed.

(* ---------- §6 有界肢（带域点正值有界·受方 q 幂增长面输入） ---------- *)

Lemma piu1866_band_bounds : forall q : Q,
  piu1866_in_band q ->
  Qlt 0 q /\ Qle piu1866_band_lo q /\ Qle q piu1866_band_hi.
Proof.
  intros q [H1 H2]. split; [| split].
  - apply (Qlt_trans 0 piu1866_band_lo q).
    + vm_compute. reflexivity.
    + exact H1.
  - exact (Qlt_le_weak _ _ H1).
  - exact (Qlt_le_weak _ _ H2).
Qed.

(* ---------- §7 阀形接口（R_W≥1 可容 c0=1 形·1862 P6 互译恒等式） ---------- *)

(* WING 坐标阀形：WING·(h+1)·(2·n_sel+2)! ≥ K/8。                        *)
Definition piu1866_valve_R1 (WING K : Q) (h n_sel : nat) : Prop :=
  Qle ((8 # 1)%Q * K)
      (WING * ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (2 * n_sel + 2)%nat)).

(* 闭式坐标阀形（互译侧）：(2/27)·b0^n·q^{2n+2}·(n+1)!·(h+1) ≥ K/8。     *)
Definition piu1866_valve_closed (b0 q : Q) (n h : nat) (K : Q) : Prop :=
  Qle ((8 # 1)%Q * K)
      ((2 # 27)%Q * q_pow b0 n * q_pow q (2 * n + 2)%nat
                   * q_fact (n + 1)%nat * (Z.of_nat (Datatypes.S h) # 1)%Q).

(* 互译恒等式前提参数位（1862 P6 形·GAPASUME）：WING 体展开积与闭式积之   *)
(* Qeq 等式。恒等式本体已由 1862 Fraction 双侧逐位认证；本闭包内          *)
(* field/ring 实例未注册，受方沿 kernel 全链闭包填充。                    *)
Definition piu1866_mirror_identity (b0 q : Q) (n h : nat) : Prop :=
  q_fact n * (lw0_Wb b0 q n 0 * (2 # 27)%Q)
    * ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (2 * n + 2)%nat)
  == (2 # 27)%Q * q_pow b0 n * q_pow q (2 * n + 2)%nat
               * q_fact (n + 1)%nat * (Z.of_nat (Datatypes.S h) # 1)%Q.

(* Qeq 传递微件（Z 交叉分子式确定性链·%Z 注记） *)
Lemma piu1866_Qeq_mult_r : forall a b c : Q, a == b -> a * c == b * c.
Proof.
  intros a b c H. unfold Qeq in *. unfold Qmult. cbn [Qnum Qden].
  rewrite !Pos2Z.inj_mul.
  transitivity ((Qnum a * Z.pos (Qden b) * (Qnum c * Z.pos (Qden c)))%Z).
  - ring.
  - rewrite H. ring.
Qed.

Lemma piu1866_Qeq_le_r : forall x y z : Q, x == y -> Qle z x -> Qle z y.
Proof.
  intros x y z Hxy Hle. unfold Qle in *. unfold Qeq in Hxy.
  assert (Dy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.is_pos.
  assert (Hm : ((Qnum z * Z.pos (Qden x) * Z.pos (Qden y)
               <= Qnum x * Z.pos (Qden z) * Z.pos (Qden y)))%Z)
    by (apply (Zmult_lt_0_le_compat_r (Qnum z * Z.pos (Qden x))
                (Qnum x * Z.pos (Qden z)) (Z.pos (Qden y)));
        [ lia | exact Hle ]).
  nia.
Qed.

Lemma piu1866_Qeq_le_l : forall x y z : Q, x == y -> Qle z y -> Qle z x.
Proof.
  intros x y z Hxy Hle. unfold Qle in *. unfold Qeq in Hxy.
  assert (Dx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.is_pos.
  assert (Hm : ((Qnum z * Z.pos (Qden y) * Z.pos (Qden x)
               <= Qnum y * Z.pos (Qden z) * Z.pos (Qden x)))%Z)
    by (apply (Zmult_lt_0_le_compat_r (Qnum z * Z.pos (Qden y))
                (Qnum y * Z.pos (Qden z)) (Z.pos (Qden x)));
        [ lia | exact Hle ]).
  nia.
Qed.

Lemma piu1866_valve_R1_mirror_facet :
  forall (WING K b0 q : Q) (n h : nat),
    WING == q_fact n * (lw0_Wb b0 q n 0 * (2 # 27)%Q) ->
    piu1866_mirror_identity b0 q n h ->
    (piu1866_valve_R1 WING K h n <-> piu1866_valve_closed b0 q n h K).
Proof.
  intros WING K b0 q n h HWing Hmirror.
  unfold piu1866_valve_R1, piu1866_valve_closed.
  assert (Hprod : WING * ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (2 * n + 2)%nat)
              == q_fact n * (lw0_Wb b0 q n 0 * (2 # 27)%Q)
                   * ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (2 * n + 2)%nat))
    by apply (piu1866_Qeq_mult_r _ _ _ HWing).
  split; intros Hle.
  - apply (piu1866_Qeq_le_r _ _ _ Hmirror).
    apply (piu1866_Qeq_le_r _ _ _ Hprod). exact Hle.
  - apply (piu1866_Qeq_le_l _ _ _ Hprod).
    apply (piu1866_Qeq_le_l _ _ _ Hmirror). exact Hle.
Qed.

(* 40h+48 坐标桥（born 件 piu1864_two_nsel_height 受方面）。             *)
Lemma piu1866_valve_R1_40h48 :
  forall (WING K : Q) (h n_sel : nat),
    (2 * n_sel + 2)%nat = (40 * h + 48)%nat ->
    piu1866_valve_R1 WING K h n_sel <->
    Qle ((8 # 1)%Q * K)
        (WING * ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (40 * h + 48)%nat)).
Proof.
  intros WING K h n_sel Hn. unfold piu1866_valve_R1. rewrite Hn.
  split; intros HH; exact HH.
Qed.

Lemma piu1866_valve_R1_height :
  forall (WING K : Q) (q : Q),
    piu1866_valve_R1 WING K (lw1m_height q) (piu1864_nsel (Qred q)) <->
    Qle ((8 # 1)%Q * K)
        (WING * ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
                 * q_fact (40 * lw1m_height q + 48)%nat)).
Proof.
  intros WING K q. apply piu1866_valve_R1_40h48.
  apply piu1864_two_nsel_height.
Qed.

(* ---------- §8 带域取样表（h=2..12 带内既约点·vm_compute 级） ---------- *)

Lemma piu1866_band_spot_table :
  piu1866_in_band (3 # 1)%Q /\ piu1866_in_band (10 # 3)%Q /\
  piu1866_in_band (16 # 5)%Q /\ piu1866_in_band (22 # 7)%Q /\
  piu1866_in_band (29 # 9)%Q /\ piu1866_in_band (35 # 11)%Q /\
  piu1866_in_band (47 # 15)%Q /\ piu1866_in_band (61 # 19)%Q /\
  piu1866_in_band (77 # 24)%Q.
Proof.
  repeat split; unfold piu1866_in_band; vm_compute; reflexivity.
Qed.

(* ---------- §9 假设闭合自检 ---------- *)

Print Assumptions piu1866_band_cert.
Print Assumptions piu1866_band_kernel_windows.
Print Assumptions piu1866_in_band_Qred_iff.
Print Assumptions piu1866_band_bounds.
Print Assumptions piu1866_valve_R1_mirror_facet.
Print Assumptions piu1866_valve_R1_height.
Print Assumptions piu1866_band_spot_table.
