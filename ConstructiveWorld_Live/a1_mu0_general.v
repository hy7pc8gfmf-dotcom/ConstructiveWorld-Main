(* 模块：a1_mu0_general.v —— π 幂率测度语句的 μ₀ 泛化与闭式证书接口定型。
   使命：把 LW1PiMeasure 主定理证体内显式选取的 μ₀=2/C=2 泛化为前提参数
   （μ₀ ≥ 2 升前提位，预算常数 C、率阈 c₀ 与预算口径 1 < C·c₀ 一并参数化）；
   将分离闭式接口面定型为库内统一闭式证书语句形（sigT 见证＋QltT 正性＋
   QeqT 钉定闭式槽＋real_lt 严格分离四段，闭式函数留显式参数位）；以 μ₀=2
   实例回代引理保既有主语句签名零迁移。
   依赖：S01_BaseRing（And/NatLe/NatLe_lift）、S02_CauchyComplete（QltT/QeqT/
   real_lt/real_const）、S03_QExp（real_metric）、S10_KVQuantTrig（real_pi_geom）、
   LW5SepComplexity（lw5n_find_ub）、LW1PiMeasure（lw1m_measure_face/
   lw1m_measure_face_r2/lw1m_b_cert_face/lw1m_dom_face/lw1m_hit_face/lw1m_nsep/
   lw1m_fuel/lw1m_dist_to_nsep/lw1m_escape_face/lw1m_escape_to_dist）。
   对标：LW1PiMeasure.v lw1m_measure_main（双前提主语句）/lw1m_measure_main_r2
   （出窗域零前提主语句）；库内 √2 闭式测度件统一主语句形。
   构造性：零公理/零承认式/零经典逻辑；新增语句面全 Set（And＋NatLe＋sigT＋
   QltT＋QeqT）；证明体沿 lw1m_dist_to_nsep/lw5n_find_ub 显式链，零 solver
   收尾；μ₀ ≥ 2 前提为语句面承载的框架下界（π 连分数收敛子 1/q_n² 反驳
   线性率，率面只承 μ₀ ≥ 2）。提取面＝两泛化语句面（原 b_cert_face 系
   real_const/real_metric 闭包面，沿 LW1PiMeasure 同款处理不入提取值域）。
   编译配方：source Live/toolchain/env.sh 后经 cpu_guard 包裹
   rocq c -native-compiler no -q -Q . "" -Q Local Local a1_mu0_general.v。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import LW5SepComplexity.
Require Import LW1PiMeasure.

(* ========== §1 全参数泛化测度语句面 ========== *)

(* 全参数泛化形：率阶 μ₀（≥2 前提承载）、预算常数 C、率阈 c₀ 与预算口径
   1 < C·c₀ 皆升前提；每 q 得预算内命中（lw1m_hit_face）与预算界
   （lw1m_nsep ≤ lw1m_fuel ≡ C·h(q)^μ₀ + 4）。证书面双前提
   lw1m_b_cert_face/lw1m_dom_face 沿 lw1m_measure_main 语句构形。 *)
Definition a1m_measure_face_gen : Set :=
  forall (mu0 C : nat) (c0 : Q),
    NatLe 2 mu0 ->
    QltT 0 c0 ->
    QltT (1 # 1) (c0 * (Z.of_nat C # 1)%Q) ->
    lw1m_b_cert_face -> lw1m_dom_face ->
    forall q : Q,
      sigT (fun _ : lw1m_hit_face q mu0 C =>
        NatLe (lw1m_nsep q mu0 C) (lw1m_fuel q mu0 C)).

(* 泛化主定理：命中分量沿 lw1m_dist_to_nsep（全参数化距离率互译机），
   预算界分量沿 lw5n_find_ub（n=0 层）；μ₀ 不入证明体选取位。 *)
Theorem a1m_measure_main_gen : a1m_measure_face_gen.
Proof.
  intros mu0 C c0 Hmu2 Hc0 Hcal Hb Hdom q.
  exists (lw1m_dist_to_nsep mu0 C c0 q Hc0 Hcal
            (Hdom Hb mu0 C c0 Hc0 Hcal q)).
  apply NatLe_lift. unfold lw1m_nsep, lw1m_fuel.
  pose proof (lw5n_find_ub q (C * lw1m_hpow q mu0 + 4)%nat 0) as Hub.
  rewrite Nat.add_0_l in Hub. exact Hub.
Qed.

(* μ₀=2 实例回代（回归桥）：原主语句面 lw1m_measure_face 由泛化主定理
   于 μ₀=2/C=2/c₀=1 实例化给出——原签名零迁移。 *)
Theorem a1m_measure_main_inst2 :
  lw1m_b_cert_face -> lw1m_dom_face -> lw1m_measure_face.
Proof.
  intros Hb Hdom.
  exists (Datatypes.S (Datatypes.S 0)).
  exists (NatLe_lift 2 2 (Nat.le_refl 2)).
  exists (Datatypes.S (Datatypes.S 0)).
  intro q.
  exact (a1m_measure_main_gen (Datatypes.S (Datatypes.S 0))
           (Datatypes.S (Datatypes.S 0)) (1 # 1)%Q
           (NatLe_lift 2 2 (Nat.le_refl 2)) id_refl id_refl Hb Hdom q).
Qed.

(* ========== §2 出窗域泛化（r2 面） ========== *)

(* 出窗域全参数形：率阶 μ₀ ≥ 2 升前提，出窗前提沿 lw1m_measure_face_r2
   构形留 ∀q 前提位；预算常数 C 留见证位。 *)
Definition a1m_measure_face_r2_gen : Set :=
  forall mu0 : nat,
    NatLe 2 mu0 ->
    sigT (fun C : nat =>
      forall q : Q,
        lw1m_escape_face q (1 # 1)%Q ->
        sigT (fun _ : lw1m_hit_face q mu0 C =>
          NatLe (lw1m_nsep q mu0 C) (lw1m_fuel q mu0 C))).

(* 出窗域泛化主定理：供给分量沿 lw1m_escape_to_dist（出窗 ⟹ 距离率，
   μ₀ 位本就参数化）接 lw1m_dist_to_nsep；预算界分量沿 lw5n_find_ub。 *)
Theorem a1m_measure_main_r2_gen : a1m_measure_face_r2_gen.
Proof.
  intros mu0 Hmu2.
  exists (Datatypes.S (Datatypes.S 0)).
  assert (Hc01 : QltT 0 (1 # 1)) by exact id_refl.
  assert (Hcal : QltT (1 # 1)
                   ((1 # 1) * (Z.of_nat (Datatypes.S (Datatypes.S 0)) # 1)%Q))
    by exact id_refl.
  intro q. intro Hesc.
  exists (lw1m_dist_to_nsep mu0 (Datatypes.S (Datatypes.S 0)) (1 # 1)%Q q
            Hc01 Hcal
            (lw1m_escape_to_dist q (1 # 1)%Q mu0 Hc01 Hesc)).
  apply NatLe_lift. unfold lw1m_nsep, lw1m_fuel.
  pose proof (lw5n_find_ub q
                (Datatypes.S (Datatypes.S 0) * lw1m_hpow q mu0 + 4)%nat 0) as Hub.
  rewrite Nat.add_0_l in Hub. exact Hub.
Qed.

(* μ₀=2 实例回代（r2 回归桥）：lw1m_measure_face_r2 原签名零迁移。 *)
Theorem a1m_measure_main_r2_inst2 : lw1m_measure_face_r2.
Proof.
  exists (Datatypes.S (Datatypes.S 0)).
  exists (NatLe_lift 2 2 (Nat.le_refl 2)).
  exact (a1m_measure_main_r2_gen (Datatypes.S (Datatypes.S 0))
           (NatLe_lift 2 2 (Nat.le_refl 2))).
Qed.

(* ========== §3 闭式证书接口定型 ========== *)

(* 统一闭式证书语句形：sigT 见证 ＋ QltT 正性 ＋ QeqT 钉定闭式 g a b ＋
   real_lt 严格分离四段，与库内 √2 闭式测度件主语句构形逐位同构
   （x := π）。闭式函数 g 留显式参数位——闭式到货后单点装填 g 即得全链。 *)
Definition a1m_bcert_closed_face (g : Q -> Q -> Q) : Set :=
  forall a b : Q, QltT 0 (Qabs b) ->
    sigT (fun c : Q =>
      And (QltT 0 c)
        (And (QeqT c (g a b))
             (real_lt (real_const c)
                (real_metric real_pi_geom (real_const (a / b)))))).

(* 消元桥：闭式证书面 ⟹ 既有分离接口面（QeqT 钉定段于桥位消去，
   lw1m_b_cert_face 原签名零迁移）。 *)
Theorem a1m_bcert_closed_to_bcert :
  forall g : Q -> Q -> Q, a1m_bcert_closed_face g -> lw1m_b_cert_face.
Proof.
  intros g Hcert a b Hab.
  destruct (Hcert a b Hab) as [c [Hc0 [Hpin Hsep]]].
  exists c. split.
  - exact Hc0.
  - exact Hsep.
Qed.

(* 闭式证书装填链：a1m_bcert_closed_face g 单点装填 ⟹ 全参数泛化测度语句。 *)
Theorem a1m_measure_main_closed :
  forall g : Q -> Q -> Q,
    a1m_bcert_closed_face g -> lw1m_dom_face -> a1m_measure_face_gen.
Proof.
  intros g Hcert Hdom.
  unfold a1m_measure_face_gen.
  intros mu0 C c0 Hmu2 Hc0 Hcal Hb Hdomq.
  exact (a1m_measure_main_gen mu0 C c0 Hmu2 Hc0 Hcal Hb Hdomq).
Qed.

(* ========== §4 在件检验（编译出口核对） ========== *)

Check a1m_measure_face_gen.
Check a1m_measure_main_gen.
Check a1m_measure_main_inst2.
Check a1m_measure_face_r2_gen.
Check a1m_measure_main_r2_gen.
Check a1m_measure_main_r2_inst2.
Check a1m_bcert_closed_face.
Check a1m_bcert_closed_to_bcert.
Check a1m_measure_main_closed.

(* ========== §5 提取＋假设审计 ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "extract".
Separate Extraction a1m_measure_face_gen a1m_measure_face_r2_gen.
Print Assumptions a1m_measure_main_gen.
Print Assumptions a1m_measure_main_inst2.
Print Assumptions a1m_measure_main_r2_gen.
Print Assumptions a1m_measure_main_r2_inst2.
Print Assumptions a1m_bcert_closed_to_bcert.
Print Assumptions a1m_measure_main_closed.
