(* ============================================================ *)
(* UpAblMetaConjBridge.v —— CJS3 席（合取件解封总装席）G4 合取件 C 侧        *)
(*   req 运输桥。按 CJS1 桥设计单 attn/_tcjs1_桥设计单-20260922.md 路线 (a)    *)
(*   字段替换运输桥施工：把 UpAblA2_LoInflation Part A（S01 RI/Id 世界）      *)
(*   沿字段替换运到具体 Real/req 世界（RealEnhancedReal 放电），产出          *)
(*   mtdc_lo_inflation 供 UpAblMetaDivThm mtd_unbounded_conj 解封接线。       *)
(*   模具=UpReqConcMixSel（库内 ums_→cmk_ 全族 req 移植先例）。               *)
(*   语句级主件 mtdc_lo_inflation（loᵢ Part A 引擎 req 转述）+ 8 镜像小件     *)
(*   （消费 cmk_ 孪件机械转述，非重证明；镜像 LoInflation :63-312 逐行）。     *)
(* 依赖：CW_ConstructiveWorld_219；UpReqAlgebra（req_minus/req_two_pos/       *)
(*   req_mult_cancel_l/req_le_mult_compat_r/req_inv_pos_mult_distr）；        *)
(*   UpReqConcMixSel（cmk_ 全族）。禁 Require UpReqUMixSelect/                *)
(*   UpAblA2_LoInflation（防 RI 名劫持）。                                    *)
(* 施工注（CJS3 对设计单骨架的两处机械落实，零语义形变）：                     *)
(*   ①设计单接线契约「封存件只加 1 行 Require」⇒ 本件对 UpReqAlgebra/         *)
(*     UpReqConcMixSel 取 Require Export（骨架为 Import——Import 不外传        *)
(*     cmk_ 名，封存件语句面 cmk_scale/cmk_r_pow 将无法解析；Export 为        *)
(*     1 行契约的机械必要，CMixSel 头注撞名检查在案，零名劫持）。             *)
(*   ②设计单桩10 骨架「Harch ub2 取 N2」与「结论取 ub2 归一形＝               *)
(*     mult mtdc_four ub2」不可同时成立（Harch ub2 只给 ub2 < k·1，           *)
(*     四倍放大后不闭合）——按设计关键「leg3=HN2 逐字直配」执行：               *)
(*     Harch 施于 mult mtdc_four ub2 取 N2（非负腿 Hub4 照 Hub2 同模）、      *)
(*     pow_tail #2 前件经 le 链 ub2 ≤ 4·ub2（1≤4 桩2）＋lt_le_trans 送达；    *)
(*     leg3=HN2 逐字。其余全骨架逐行镜像。                                    *)
(* 证书同源注（设计单步骤 0 探针裁决执行）：mtdc_inv2 证书统一取              *)
(*   req_two_pos（UpReqAlgebra:340，封存件 mtd_inv2 :1451 同源），            *)
(*   Hlohalf0 内 inv_pos_pos 证书同取 req_two_pos——保 mtd_inv2≡mtdc_inv2、   *)
(*   G4 语句面证书链与本桥旗舰结论纯 δ 可换（Qed 证书名零混用）。             *)
(* 红线自审：Set 层零 Prop（量词 Real/nat、lt/le/sigT/And 全 Set 面，         *)
(*   Or 注入 inl）；零 Axiom/Admitted；零经典逻辑；零 Obj.magic 面            *)
(*   （提取铸型若现，按 CJS2 G3 判例归 (a) 族「双世界接口面证明项擦除        *)
(*   铸型」登记）；旗舰 Defined 可提取。                                     *)
(* 编译配方（9.1 直调轨）：unset COQLIB/ROCQLIB；coqc -q -native-compiler no  *)
(*   -Q . "" UpAblMetaConjBridge.v（cpu_guard 包裹，coqc<3 让行）。           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Export UpReqAlgebra.
Require Export UpReqConcMixSel.
Import RealInterfaceEnhancedMod.

(* ===== §0 放电与环账桥 ===== *)
(* 实例 RealEnhancedReal（S07:8591）经上行 Import 已全局在位，投影零新桩。   *)
(* mtdc_mult_distr_r：Setoid distrib 字段一跳（comm+congr），                *)
(*   镜像 S01 mult_plus_distr_r（右分配，S01:399）req 面。                   *)

Lemma mtdc_mult_distr_r : forall a b c : Real,
  req (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  apply (req_trans _ (mult c (plus a b))).
  { exact (mult_comm (plus a b) c). }
  apply (req_trans _ (plus (mult c a) (mult c b))).
  { exact (distrib c a b). }
  exact (req_plus_compat (mult c a) (mult a c) (mult c b) (mult b c)
           (mult_comm c a) (mult_comm c b)).
Defined.

(* ===== §1 常数面（体与封存件 mtd_inv2/mtd_four :1451-1452 δ 全同） ===== *)
(* mtdc_inv2 证书统一取 req_two_pos（见头注证书同源注）。                     *)

Definition mtdc_two : Real := plus one one.
Definition mtdc_inv2 : Real := inv_pos mtdc_two req_two_pos.
Definition mtdc_four : Real := plus mtdc_two mtdc_two.

(* ===== §2 loᵢ Part A 引擎 req 转述（Section 面逐字镜像 LoInflation :63-312） ===== *)
(* 出节签名（镜像 LoInflation 变参序，与封存块 L1503 消费位同形）：           *)
(*   mtdc_lo_inflation lt_plus_compat_lt_le TV0 Htv0 budget Hbudget          *)
(*                     lo Hlo0 Hds1 Harch                                     *)

Section ConjBridge.

(* 诚实接口：混合 lt+le 加法保序（LoInflation :77 同位 Variable 镜像；       *)
(*   出节后由封存件 mtd_lpc :1441 填槽）                                     *)
Variable lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ---- 固定面：TV₀ / budget（:80-84 镜像） ---- *)
Variable TV0 : Real.
Variable Htv0 : le zero TV0.
Variable budget : Real.
Variable Hbudget : lt zero budget.

(* ---- 膨胀参数：lo（:87-89 镜像） ---- *)
Variable lo : Real.
Variable Hlo0 : lt zero lo.
Variable Hds1 : lt (mult lo lo) one.   (* δ* < 1：Doeblin 证书 *)

(* Arch 前件（:92-93 镜像；nat-尺度 cmk_scale 形——封存块 L1467 换名后同形） *)
Variable Harch : forall x : Real, le zero x ->
  sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)).

(* ---- 常数证书（:96-101 镜像；two/inv2/four 已上移 §1 顶层） ---- *)
Let Htwopos : lt zero mtdc_two := plus_positive one one one_pos one_pos.
Let Hfourpos : lt zero mtdc_four :=
  plus_positive mtdc_two mtdc_two Htwopos Htwopos.
Let inv4 := inv_pos mtdc_four Hfourpos.

(* ---- 两配置：lo 与 lo/2；δ* := lo² 与 δ*₂ := (lo/2)²（:104-108 镜像） ---- *)
Let loh := mult lo mtdc_inv2.
Let ds := mult lo lo.
Let ds2 := mult loh loh.
Let kap := req_minus one ds.
Let kap2 := req_minus one ds2.

(* ---- 两配置的 Arch 输入 = 选择器显式 k-上界（:111-120 镜像） ---- *)
Let Hds0 : lt zero ds := mult_positive lo lo Hlo0 Hlo0.
Let Hwb : lt zero (mult ds budget) :=
  mult_positive ds budget Hds0 Hbudget.
Let ub := mult TV0 (inv_pos (mult ds budget) Hwb).
(* 证书同源：inv_pos_pos 槽取 req_two_pos（封存块 L1486-1490 同源，纯 δ） *)
Let Hlohalf0 : lt zero loh :=
  mult_positive lo mtdc_inv2 Hlo0 (inv_pos_pos mtdc_two req_two_pos).
Let Hds2_0 : lt zero ds2 := mult_positive loh loh Hlohalf0 Hlohalf0.
Let Hwb2 : lt zero (mult ds2 budget) :=
  mult_positive ds2 budget Hds2_0 Hbudget.
Let ub2 := mult TV0 (inv_pos (mult ds2 budget) Hwb2).

(* ---------- 桩2 基础序小件（镜像 :125-135 loi_le_one_four） ---------- *)

Lemma mtdc_le_one_four : le one mtdc_four.
Proof.
  apply (le_trans one (plus one one) mtdc_four).
  - exact (cmk_le_plus_r one one (lt_le_iff zero one (inl one_pos))).
  - exact (cmk_le_plus_r mtdc_two mtdc_two
             (le_id_l zero (plus zero zero) mtdc_two
                (req_sym _ _ (plus_zero zero))
                (le_plus_compat zero one zero one
                   (lt_le_iff zero one (inl one_pos))
                   (lt_le_iff zero one (inl one_pos))))).
Qed.

(* ---------- 桩3/桩4 环账小件（镜像 :140-154） ---------- *)

Lemma mtdc_inv2_two : req (mult mtdc_two mtdc_inv2) one.
Proof.
  exact (inv_pos_correct mtdc_two req_two_pos).
Qed.

Lemma mtdc_inv2_four_two : req (mult mtdc_inv2 mtdc_four) mtdc_two.
Proof.
  apply (req_trans _ (mult mtdc_four mtdc_inv2)).
  { exact (mult_comm mtdc_inv2 mtdc_four). }
  apply (req_trans _ (plus (mult mtdc_two mtdc_inv2)
                           (mult mtdc_two mtdc_inv2))).
  { exact (mtdc_mult_distr_r mtdc_two mtdc_two mtdc_inv2). }
  apply (req_trans _ (plus one one)).
  { exact (req_plus_compat (mult mtdc_two mtdc_inv2) one
                           (mult mtdc_two mtdc_inv2) one
             (inv_pos_correct mtdc_two req_two_pos)
             (inv_pos_correct mtdc_two req_two_pos)). }
  exact (req_refl (plus one one)).
Qed.

(* ---------- 桩5 逆元外延（镜像 :157-167 loi_inv_wd；                       *)
(*    mult_cancel_l→req_mult_cancel_l，id 链→req_trans＋cmk_mult_congr）---- *)

Lemma mtdc_inv_wd : forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
  req a b -> req (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hab.
  apply (req_mult_cancel_l b (inv_pos a Ha) (inv_pos b Hb) Hb).
  exact (req_trans _ _ _
           (req_trans _ _ _
              (cmk_mult_congr_r (inv_pos a Ha) b a (req_sym _ _ Hab))
              (inv_pos_correct a Ha))
           (req_sym _ _ (inv_pos_correct b Hb))).
Qed.

(* ---------- 桩6 δ* 减半律：(lo/2)²·4 == lo²（镜像 :170-202                  *)
(*    loi_ds2_scale 全链 H1-H6，id→req 机械换名，约 35 行零数学新内容） ---- *)

Lemma mtdc_ds2_scale : req (mult mtdc_four ds2) ds.
Proof.
  assert (H1 : req (mult mtdc_four loh) (mult lo mtdc_two)).
  { exact (req_trans _ _ _
             (mult_assoc mtdc_four lo mtdc_inv2)
             (req_trans _ _ _
                (req_mult_compat (mult mtdc_four lo) (mult lo mtdc_four)
                                 mtdc_inv2 mtdc_inv2
                   (mult_comm mtdc_four lo) (req_refl mtdc_inv2))
                (req_trans _ _ _
                   (req_sym _ _ (mult_assoc lo mtdc_four mtdc_inv2))
                   (cmk_mult_congr_l lo (mult mtdc_four mtdc_inv2) mtdc_two
                      (req_trans _ _ _ (mult_comm mtdc_four mtdc_inv2)
                                       mtdc_inv2_four_two))))). }
  assert (H2 : req (mult mtdc_four (mult loh loh))
                  (mult (mult mtdc_four loh) loh)).
  { exact (mult_assoc mtdc_four loh loh). }
  assert (H3 : req (mult (mult mtdc_four loh) loh)
                  (mult (mult lo mtdc_two) loh)).
  { exact (req_mult_compat (mult mtdc_four loh) (mult lo mtdc_two)
                           loh loh H1 (req_refl loh)). }
  assert (H4 : req (mult (mult lo mtdc_two) loh)
                  (mult (mult (mult lo mtdc_two) lo) mtdc_inv2)).
  { exact (mult_assoc (mult lo mtdc_two) lo mtdc_inv2). }
  assert (H5 : req (mult (mult (mult lo mtdc_two) lo) mtdc_inv2)
                  (mult (mult (mult lo lo) mtdc_two) mtdc_inv2)).
  { exact (req_trans _ _ _
             (req_mult_compat (mult (mult lo mtdc_two) lo)
                              (mult lo (mult mtdc_two lo))
                              mtdc_inv2 mtdc_inv2
                (req_sym _ _ (mult_assoc lo mtdc_two lo))
                (req_refl mtdc_inv2))
             (req_mult_compat (mult lo (mult mtdc_two lo))
                              (mult (mult lo lo) mtdc_two)
                              mtdc_inv2 mtdc_inv2
                (req_trans _ _ _
                   (cmk_mult_congr_l lo (mult mtdc_two lo) (mult lo mtdc_two)
                      (mult_comm mtdc_two lo))
                   (mult_assoc lo lo mtdc_two))
                (req_refl mtdc_inv2))). }
  assert (H6 : req (mult (mult (mult lo lo) mtdc_two) mtdc_inv2) ds).
  { exact (req_trans _ _ _
             (req_sym _ _ (mult_assoc (mult lo lo) mtdc_two mtdc_inv2))
             (req_trans _ _ _
                (cmk_mult_congr_l (mult lo lo) (mult mtdc_two mtdc_inv2) one
                   mtdc_inv2_two)
                (mult_one (mult lo lo)))). }
  exact (req_trans _ _ _ (req_trans _ _ _ (req_trans _ _ _ H2 H3) H4)
           (req_trans _ _ _ H5 H6)).
Qed.

(* ---------- 桩7 (lo/2)² ≤ lo²（镜像 :205-215；                              *)
(*    le_mult_compat_r→req_le_mult_compat_r） ---------- *)

Lemma mtdc_ds2_le_ds : le ds2 ds.
Proof.
  apply (le_trans ds2 (mult ds2 one) ds).
  - exact (le_id_r ds2 ds2 (mult ds2 one)
             (req_sym _ _ (mult_one ds2)) (le_refl ds2)).
  - apply (le_trans (mult ds2 one) (mult ds2 mtdc_four) ds).
    + exact (req_le_mult_compat_r ds2 one mtdc_four
               (lt_le_iff zero ds2 (inl Hds2_0)) mtdc_le_one_four).
    + exact (le_id_l (mult ds2 mtdc_four) ds ds
               (req_trans _ _ _ (mult_comm ds2 mtdc_four) mtdc_ds2_scale)
               (le_refl ds)).
Qed.

(* ---------- 桩8 δ*₂ < 1（κ₂ 证书；镜像 :218-221 一跳） ---------- *)

Lemma mtdc_ds2_lt_one : lt ds2 one.
Proof.
  exact (le_lt_trans ds2 ds one mtdc_ds2_le_ds Hds1).
Qed.

(* ---------- 桩9 核心四倍律：ub(lo/2) == 4·ub(lo)（镜像 :225-259；           *)
(*    inv_pos_mult_distr→req_inv_pos_mult_distr、loi_inv_wd→桩5、            *)
(*    ums_mult_one_l→cmk_mult_one_l，其余 Setoid 同名，约 40 行） ---------- *)

Lemma mtdc_ub2_quad : req ub2 (mult mtdc_four ub).
Proof.
  assert (Hsplit : req (mult ds budget)
                       (mult mtdc_four (mult ds2 budget))).
  { exact (req_trans _ _ _
             (req_mult_compat ds (mult mtdc_four ds2) budget budget
                (req_sym _ _ mtdc_ds2_scale) (req_refl budget))
             (req_sym _ _ (mult_assoc mtdc_four ds2 budget))). }
  assert (Hbinv : req (inv_pos (mult ds budget) Hwb)
                      (mult inv4 (inv_pos (mult ds2 budget) Hwb2))).
  { exact (req_trans _ _ _
             (mtdc_inv_wd (mult ds budget)
                          (mult mtdc_four (mult ds2 budget))
                          Hwb
                          (mult_positive mtdc_four (mult ds2 budget)
                             Hfourpos Hwb2)
                          Hsplit)
             (req_inv_pos_mult_distr mtdc_four (mult ds2 budget)
                                     Hfourpos Hwb2)). }
  assert (Hub' : req ub (mult inv4 ub2)).
  { exact (req_trans _ _ _
             (cmk_mult_congr_l TV0 (inv_pos (mult ds budget) Hwb)
                (mult inv4 (inv_pos (mult ds2 budget) Hwb2)) Hbinv)
             (req_trans _ _ _
                (mult_assoc TV0 inv4 (inv_pos (mult ds2 budget) Hwb2))
                (req_trans _ _ _
                   (req_mult_compat (mult TV0 inv4) (mult inv4 TV0)
                      (inv_pos (mult ds2 budget) Hwb2)
                      (inv_pos (mult ds2 budget) Hwb2)
                      (mult_comm TV0 inv4) (req_refl _))
                   (req_sym _ _ (mult_assoc inv4 TV0
                                   (inv_pos (mult ds2 budget) Hwb2)))))). }
  assert (Hfin : req (mult mtdc_four (mult inv4 ub2)) ub2).
  { exact (req_trans _ _ _
             (mult_assoc mtdc_four inv4 ub2)
             (req_trans _ _ _
                (req_mult_compat (mult mtdc_four inv4) one ub2 ub2
                   (inv_pos_correct mtdc_four Hfourpos) (req_refl ub2))
                (cmk_mult_one_l ub2))). }
  exact (req_sym _ _ (req_trans _ _ _
           (cmk_mult_congr_l mtdc_four ub (mult inv4 ub2) Hub') Hfin)).
Qed.

(* ---------- 桩10 旗舰：膨胀律（G4 归一形：结论 leg3 取 ub2 归一形，          *)
(*    与解封句 exact 直配——设计单【设计关键】；镜像 :265-312，                *)
(*    pow_tail 双放电 cmk_pow_tail（Heqk 槽 req 形：kap 定义性 req_refl）--- *)

Theorem mtdc_lo_inflation :
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (cmk_r_pow kap k1) TV0) budget)
        (And (lt (mult (cmk_r_pow kap2 k2) TV0) budget)
             (lt (mult mtdc_four ub2) (cmk_scale k2 one))))).
Proof.
  assert (Hub : le zero ub).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds budget) Hwb))
             (mult TV0 (inv_pos (mult ds budget) Hwb))
             (req_sym _ _ (req_trans _ _ _
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
             (req_sym _ _ (req_trans _ _ _
                (mult_comm zero (inv_pos (mult ds2 budget) Hwb2))
                (mult_zero (inv_pos (mult ds2 budget) Hwb2))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds2 budget) Hwb2)
                (lt_le_iff zero (inv_pos (mult ds2 budget) Hwb2)
                             (inl (inv_pos_pos (mult ds2 budget) Hwb2)))
                Htv0)). }
  (* 归一形非负腿：0 ≤ 4·ub2（4·ub2 ≡ TV0·(4·inv(ds2·budget)) 换形后同模） *)
  assert (Hub4 : le zero (mult mtdc_four ub2)).
  { assert (HX2p : lt zero (inv_pos (mult ds2 budget) Hwb2))
      by exact (inv_pos_pos (mult ds2 budget) Hwb2).
    assert (Hchain : req (mult mtdc_four ub2)
                         (mult TV0 (mult mtdc_four
                                       (inv_pos (mult ds2 budget) Hwb2)))).
    { exact (req_trans _ _ _
               (mult_assoc mtdc_four TV0
                  (inv_pos (mult ds2 budget) Hwb2))
               (req_trans _ _ _
                  (cmk_mult_congr_r (inv_pos (mult ds2 budget) Hwb2)
                     (mult mtdc_four TV0) (mult TV0 mtdc_four)
                     (mult_comm mtdc_four TV0))
                  (req_sym _ _ (mult_assoc TV0 mtdc_four
                                  (inv_pos (mult ds2 budget) Hwb2))))). }
    assert (Hub4' : le zero
               (mult TV0 (mult mtdc_four
                             (inv_pos (mult ds2 budget) Hwb2)))).
    { exact (le_id_l zero
               (mult zero (mult mtdc_four
                              (inv_pos (mult ds2 budget) Hwb2)))
               (mult TV0 (mult mtdc_four
                             (inv_pos (mult ds2 budget) Hwb2)))
               (req_sym _ _ (req_trans _ _ _
                  (mult_comm zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))
                  (mult_zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))))
               (le_mult_compat_weak zero TV0
                  (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2))
                  (lt_le_iff zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2))
                     (inl (mult_positive mtdc_four
                            (inv_pos (mult ds2 budget) Hwb2)
                            Hfourpos HX2p)))
                  Htv0)). }
    exact (le_id_r zero
             (mult TV0 (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))
             (mult mtdc_four ub2)
             (req_sym _ _ Hchain) Hub4'). }
  (* ub2 ≤ 4·ub2（1 ≤ 4 桩2 ＋ 弱乘单调） *)
  assert (Hub2le : le ub2 (mult mtdc_four ub2)).
  { exact (le_id_l ub2 (mult one ub2) (mult mtdc_four ub2)
             (req_sym _ _ (cmk_mult_one_l ub2))
             (le_mult_compat_weak one mtdc_four ub2 Hub2
                mtdc_le_one_four)). }
  destruct (Harch ub Hub) as [N1 HN1].
  destruct (Harch (mult mtdc_four ub2) Hub4) as [N2 HN2].
  destruct (cmk_pow_tail lt_plus_compat_lt_le kap TV0 budget ds N1 Hwb
              Hds0 Hds1 (req_refl kap) Htv0
              (lt_le_iff zero budget (inl Hbudget)) HN1) as [k1 Hk1].
  pose (Hp2 := cmk_pow_tail lt_plus_compat_lt_le kap2 TV0 budget ds2 N2
                 Hwb2 Hds2_0 mtdc_ds2_lt_one (req_refl kap2) Htv0
                 (lt_le_iff zero budget (inl Hbudget))
                 (le_lt_trans ub2 (mult mtdc_four ub2)
                    (cmk_scale (Datatypes.S N2) one) Hub2le HN2)).
  exists k1. exists (projT1 Hp2). split.
  - exact Hk1.
  - split.
    + exact (projT2 Hp2).
    + exact HN2.
Defined.

End ConjBridge.

(* ============================================================ *)
(* G2/G3 审计口：PA 预期 Closed（零 Axiom、全 Set 层证书）                      *)
(* ============================================================ *)

Print Assumptions mtdc_lo_inflation.
