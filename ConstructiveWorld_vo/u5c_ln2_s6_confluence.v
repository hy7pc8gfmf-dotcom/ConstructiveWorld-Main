(* ===================================================================== *)
(*  u5c_ln2_s6_confluence.v —— ln2 合流强化：Hbint 供位接入六肢合流面        *)
(*  （条件 inhabited 升强化形）                                              *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_s6_confluence。                                       *)
(*  使命：Hbint 供位（s5e_hbint）接入合流面，合流重铸照 L5 刻形清单：      *)
(*    ①B 伴位由 s5e_hbint 见证族构造（s6_Bz := projT1 ∘ s5e_hbint）——      *)
(*      B 位零自由参数、整性 by construction（s6_Bz_spec），B-整性障碍      *)
(*      （2^{n+1}bv_p n 非整）从此在正典实例面机械闭合；                    *)
(*    ②五层供给面条件 inhabited 升强化形 s6_supply_inhabited_strong：      *)
(*      实例三钉 X:=ri_real（RealIdentity，与 Ln2Bridge.ln2b_X 同定义面）   *)
(*      ＋A:=s5d_lna（Λ 清分母刻形）＋B:=s6_Bz（Hbint 见证族）；            *)
(*      六肢逐位：①gap2_theta_45_lt1／②′s5d_canA_abs_pos／                *)
(*      ③u5c_ln2_witness_pos／④s4f_content 在正典实例实例化／              *)
(*      ⑤s5c_clo_lt_carrier／⑥u5c_ln2_theta_slot_face_of_budget——         *)
(*      全部为已注册件直接复用，零重做；                                    *)
(*    ③Hrho/Hbudget 两位 Observable 刻形不变（GAPASUME 冻结维持——          *)
(*      n≥2 无 W 已由 L6 件①证得）：仅在正典实例重刻（s4f_rho              *)
(*      ri_real s5d_lna s6_Bz 与 u5c_ln2b_line ri_real s5d_lna s6_Bz）。   *)
(*  实现注记：六肢逐位走 u5c_gap2_bridge 装配面；数值锚为抽象 Z 见证       *)
(*    projT1 (s5e_hbint n) 的数值钉形（QeqT 传递链机证）。                  *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、BeukersLists、        *)
(*    u5c_ln2_gap2_bridge、u5c_ln2_assembly、u5c_ln2_s4fill、              *)
(*    u5c_ln2_s5c_supply、u5c_ln2_witness、u5c_ln2_theta_slot、             *)
(*    abl_ln2_reorder、abl_ln2_reorder_assembly、abl_ln2_bsum_cauchy、      *)
(*    u5c_ln2_s5d_shape、u5c_ln2_s5e_hbint、RealIdentity；                  *)
(*    Stdlib：QArith/Qabs/ZArith/Arith。                                    *)
(*  对标：u5c_gap2_slot 五槽形态（u5c_ln2_gap2_bridge.v:155）；             *)
(*    s5c_supply_inhabited 合流前形（u5c_ln2_s5c_supply）。                 *)
(*  数值锚：s6_runalive_Bz3／Bz4 于 n=3/4 钉形 =4192／=85440               *)
(*    （沿 s6_Bz_spec＋s5e_runalive_z3/z4 QeqT 传递链机证；                 *)
(*    精确有理算术独立复算 L6 账在卷）。                                    *)
(*  构造性注记：零承认、零经典逻辑、零 solver；s6_Bz 为构造性投影组合。     *)
(*  诚实边界：无条件 inhabited 与件④去参数化收束（ln2b_irrational_from_    *)
(*    supply）仍冻结于勘录②通 n 闭式合一（供给链主缺口）之后，本件不冒领；  *)
(*    ④肢读出面迁移小件（u5c_ln2_seam4_sline_form＋ln2b_X_proj 同义迁移）   *)
(*    属更深 Ln2Bridge 装配集成，非合流定理所需，留候铸登记。               *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_s6_confluence.v *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import BeukersLists.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_assembly.
Require Import u5c_ln2_s4fill.
Require Import u5c_ln2_s5c_supply.
Require Import u5c_ln2_witness.
Require Import u5c_ln2_theta_slot.
Require Import abl_ln2_reorder.
Require Import abl_ln2_reorder_assembly.
Require Import abl_ln2_bsum_cauchy.
Require Import u5c_ln2_s5d_shape.
Require Import u5c_ln2_s5e_hbint.
Require Import RealIdentity.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 Hbint 供位接入位：B 伴位见证族构造                                     *)
(* ============================================================ *)

(* B'_n 的 Z 见证：s5e_hbint n 的第一投影（构造性·零前提） *)
Definition s6_Bz (n : nat) : Z := projT1 (s5e_hbint n).

(* 见证规格：s6_Bz n 与 Λ-清分母 B 伴位（Q 面正形）逐点一致 *)
Theorem s6_Bz_spec : forall n : nat, QeqT (s5d_bq n) ((s6_Bz n # 1)%Q).
Proof. intro n. unfold s6_Bz. exact (projT2 (s5e_hbint n)). Qed.

(* ============================================================ *)
(* §1 合流强化主件：正典 ln2 实例六肢逐位（条件 inhabited 强化形）            *)
(* ============================================================ *)

Theorem s6_supply_inhabited_strong :
  (forall (n : nat) (eps : Q), QltT 0 eps ->
     sigT (fun N : nat => forall k : nat, NatLe N k ->
             QltT (Qabs (s4f_rho ri_real s5d_lna s6_Bz n k)) eps)) ->
  (forall n : nat,
     real_le (u5c_ln2b_line ri_real s5d_lna s6_Bz n)
             (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  u5c_ln2i_pade_supply ri_real.
Proof.
  intros Hrho Hbudget.
  apply (u5c_gap2_bridge ri_real s5d_lna s6_Bz u5c_ln2_clo_witness (4 # 5)%Q
           (u5c_lns_Ibreal lns_bsum lnb2_cauchy)).
  unfold u5c_gap2_slot.
  split.
  - (* ① θ = 4/5 < 1（generic born） *)
    exact gap2_theta_45_lt1.
  - split.
    + (* ②′ 0 < |A'_n| 在 Λ 清分母位（s5d born） *)
      intro n. apply s5d_canA_abs_pos.
    + split.
      * (* ③ 0 < clo_n（generic born） *)
        intro n. apply u5c_ln2_witness_pos.
      * split.
        -- (* ④ 缝：真族载体 ≈ 正典线值读数（s4fill generic 在正典实例实例化） *)
           intro n. exact (s4f_content ri_real s5d_lna s6_Bz n (Hrho n)).
        -- split.
           ++ (* ⑤ 下界肢：clo_n < 真族载体（s5c born generic） *)
              intro n. exact (inl (s5c_clo_lt_carrier n)).
           ++ (* ⑥ 上界肢：预算 face 一次代入（theta_slot born generic） *)
              intro n.
              exact (u5c_ln2_theta_slot_face_of_budget ri_real s5d_lna s6_Bz
                       (u5c_lns_Ibreal lns_bsum lnb2_cauchy)
                       (fun n0 : nat => s4f_content ri_real s5d_lna s6_Bz n0 (Hrho n0))
                       Hbudget n).
Qed.

(* ============================================================ *)
(* §2 RunAlive 数值锚：抽象 Z 见证的数值钉形                                  *)
(* ============================================================ *)

(* n=3：projT1 (s5e_hbint 3) = 4192（与 s5d_runalive_bq3／s5e_runalive_z3 一致） *)
Theorem s6_runalive_Bz3 : QeqT ((s6_Bz 3 # 1)%Q) ((4192 # 1)%Q).
Proof.
  apply (gap2_qeqT_trans _ (s5d_bq 3)).
  - apply qeq_imp_qeqT. exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ (s6_Bz_spec 3))).
  - exact s5e_runalive_z3.
Qed.

(* n=4：projT1 (s5e_hbint 4) = 85440（与 s5e_runalive_z4 一致） *)
Theorem s6_runalive_Bz4 : QeqT ((s6_Bz 4 # 1)%Q) ((85440 # 1)%Q).
Proof.
  apply (gap2_qeqT_trans _ (s5d_bq 4)).
  - apply qeq_imp_qeqT. exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ (s6_Bz_spec 4))).
  - exact s5e_runalive_z4.
Qed.

(* ============================================================ *)
(* §3 提取与假设审计                                                       *)
(* ============================================================ *)

Separate Extraction s6_Bz.

Print Assumptions s6_Bz_spec.
Print Assumptions s6_supply_inhabited_strong.
Print Assumptions s6_runalive_Bz3.
Print Assumptions s6_runalive_Bz4.
