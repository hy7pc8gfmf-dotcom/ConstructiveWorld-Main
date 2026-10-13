(* 五字段指针｜模块：piu1880_egel_release.v。
   数学使命：A3 缺件①之 1868 证书承载位显式释放——eps1-min 四支肢
   （:5509 eps1 = Qmin eg (Qmin el (Qmin (1/3) ((1/2)/K)))·eg/el 占
   前两支）中 eg/el 两槽的闭式选取：带域前提下取
   eg := el := piu1880_egel_sel WING K := WING/(2K)（Q 层可判定形），
   ①1862 证书前提 `WING/(2K) ≤ eg,el` 由选取构造性零承载（Qle_refl）；
   ②与 valve_R1 的传递链（piu1872_valve_R1_leg：4/den ≤ WING/(2K)）
   合成 4/den ≤ eg,el（cert_from_WING 在闭式选取下的前提免除实例）；
   ③eps1-min 四支肢全支放行（piu1872_eps1_leg：valve_up＋den_ge24
   支 3/4 支）；
   ④带域面终形：1868 Section margin wit1 参数位在闭式选取下全实例——
   `1/den_h ≤ wit(eps1 闭式)`（piu1880_band_margin_released·带域前提
   在语句面承载——链面语义＝1862 §带内账 W1-α″ 证书条件释放位；
   release 肢本体坐标面无带域依赖·诚实注记）；
   ⑤合流肢：与 1879 字面释放模式（eg:=el:=1/60）的联合肢——
   附加 WING/(2K) ≤ 1/60 时本件坐标式释放给出 1879 字面式下界。
   依赖：Stdlib QArith/Qminmax/Lia/ZArith；S03_QExp；LW1PiMeasure；
   leibsep_nsel_h_coupling；leibsep_band_domain（piu1866_valve_R1/
   piu1866_in_band·1866 born 只读）；leibsep_band_ck_assembly
   （piu1872_valve_R1_leg/eps1_leg/den_ge24/band_margin_wit1·1872
   world 只读）；piu1880_valve_qchain（本件前置依赖·同沙箱）。对标：mathlib/stdlib 无直接对应；证书条件释放面同 LW0LeibSeparation :5509 eps1-min。
   构造性：零公理/零承认式/零经典逻辑；Q 面收尾 Qle_trans/Qle_refl；
   nat 面 lia＋piu1864_nsel_qden/Pos2Nat.is_pos 桥（1872 §8 同款）。
   编译配方：同 piu1880_valve_qchain（cwd 本件沙箱·cpu_guard v3 包裹）。
   命名：piu1880_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith.
Require Import S03_QExp.
Require Import LW1PiMeasure.
Require Import leibsep_nsel_h_coupling.
Require Import leibsep_band_domain.
Require Import leibsep_band_ck_assembly.
Require Import piu1880_valve_qchain.

(* ---------- §1 闭式选取定义 ---------- *)

Definition piu1880_egel_sel (WING K : Q) : Q := WING / (2 * K)%Q.

(* ---------- §2 释放主件（den 面：1868 承载位四支肢·闭式选取） ---------- *)

Theorem piu1880_egel_release : forall (WING K : Q) (h n_sel : nat),
  Qlt 0 K -> (2 <= n_sel)%nat ->
  piu1872_valve_up K h n_sel ->
  piu1866_valve_R1 WING K h n_sel ->
  Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) (piu1880_egel_sel WING K)
  /\ Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) (piu1880_egel_sel WING K)
  /\ Qle ((4 # 1)%Q / piu1872_valve_den h n_sel)
          (piu1872_eps1 (piu1880_egel_sel WING K)
                        (piu1880_egel_sel WING K) K).
Proof.
  intros WING K h n_sel HK Hns Hup HR1.
  pose proof (piu1872_valve_R1_leg WING K h n_sel HK HR1) as Hleg.
  assert (Heg : Qle ((4 # 1)%Q / piu1872_valve_den h n_sel)
                     (piu1880_egel_sel WING K)).
  { unfold piu1880_egel_sel.
    apply (Qle_trans _ (WING / (2 * K)%Q) (WING / (2 * K)%Q));
      [ exact Hleg | apply Qle_refl ]. }
  assert (Hel : Qle ((4 # 1)%Q / piu1872_valve_den h n_sel)
                     (piu1880_egel_sel WING K)) by exact Heg.
  split; [ exact Heg | split; [ exact Hel | ] ].
  unfold piu1880_egel_sel.
  apply (piu1872_eps1_leg (WING / (2 * K)%Q) (WING / (2 * K)%Q) K
           (piu1872_valve_den h n_sel));
    [ exact Heg | exact Hel | exact HK | exact Hup
    | apply piu1872_den_ge24; exact Hns ].
Qed.

(* ---------- §3 高度坐标面（40h+48 换算·1864 耦合桥经件②） ---------- *)

Theorem piu1880_egel_release_height : forall (q WING K : Q),
  Qlt 0 K ->
  piu1872_valve_up K (lw1m_height q) (piu1864_nsel (Qred q)) ->
  piu1866_valve_R1 WING K (lw1m_height q) (piu1864_nsel (Qred q)) ->
  Qle ((4 # 1)%Q / ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
        * q_fact (40 * lw1m_height q + 48)%nat)%Q)
       (piu1872_eps1 (piu1880_egel_sel WING K)
                     (piu1880_egel_sel WING K) K).
Proof.
  intros q WING K HK Hup HR1.
  assert (Hns2 : (2 <= piu1864_nsel (Qred q))%nat).
  { pose proof (piu1864_nsel_qden (Qred q)) as Hn.
    pose proof (Pos2Nat.is_pos (Qden (Qred q))) as Hp. lia. }
  pose proof (piu1880_egel_release WING K (lw1m_height q)
                (piu1864_nsel (Qred q)) HK Hns2 Hup HR1) as [_ [_ Heps1]].
  apply (piu1872_Qeq_le_swap _ _ _
           (piu1880_Qeq_div_r (4 # 1)%Q _ _ (piu1880_valve_den_height_conv q))).
  exact Heps1.
Qed.

(* ---------- §4 带域面终形（1868 Section margin wit1 参数位全实例） ---------- *)

Theorem piu1880_band_margin_released : forall (q WING K : Q),
  piu1866_in_band q ->
  Qlt 0 K ->
  piu1872_valve_up K (lw1m_height q) (piu1864_nsel (Qred q)) ->
  piu1866_valve_R1 WING K (lw1m_height q) (piu1864_nsel (Qred q)) ->
  Qle (1 / piu1880_den_h q)%Q
      (piu1872_wit (piu1872_eps1 (piu1880_egel_sel WING K)
                                 (piu1880_egel_sel WING K) K)).
Proof.
  intros q WING K Hband HK Hup HR1.
  assert (Hns2 : (2 <= piu1864_nsel (Qred q))%nat).
  { pose proof (piu1864_nsel_qden (Qred q)) as Hn.
    pose proof (Pos2Nat.is_pos (Qden (Qred q))) as Hp. lia. }
  pose proof (piu1880_egel_release WING K (lw1m_height q)
                (piu1864_nsel (Qred q)) HK Hns2 Hup HR1) as [Heg [Hel _]].
  unfold piu1880_den_h.
  exact (piu1872_band_margin_wit1 (piu1864_nsel (Qred q)) (lw1m_height q)
           (piu1880_egel_sel WING K) (piu1880_egel_sel WING K) K
           (piu1872_eps1 (piu1880_egel_sel WING K)
                         (piu1880_egel_sel WING K) K)
           Hns2 HK eq_refl Hup Heg Hel).
Qed.

(* ---------- §5 合流肢（1879 字面模式 eg:=el:=1/60 联合） ---------- *)

Theorem piu1880_egel_release_lit60 : forall (WING K : Q) (h n_sel : nat),
  Qlt 0 K -> (2 <= n_sel)%nat ->
  piu1872_valve_up K h n_sel ->
  piu1866_valve_R1 WING K h n_sel ->
  Qle (piu1880_egel_sel WING K) (1 # 60)%Q ->
  Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) (1 # 60)%Q.
Proof.
  intros WING K h n_sel HK Hns Hup HR1 H60.
  apply (Qle_trans _ (piu1880_egel_sel WING K) (1 # 60)%Q).
  - apply (proj1 (piu1880_egel_release WING K h n_sel HK Hns Hup HR1)).
  - exact H60.
Qed.

(* ========== 编译出口核对 ========== *)

Check piu1880_egel_sel.
Check piu1880_egel_release.
Check piu1880_egel_release_height.
Check piu1880_band_margin_released.
Check piu1880_egel_release_lit60.

Print Assumptions piu1880_egel_release.
Print Assumptions piu1880_egel_release_height.
Print Assumptions piu1880_band_margin_released.
Print Assumptions piu1880_egel_release_lit60.
