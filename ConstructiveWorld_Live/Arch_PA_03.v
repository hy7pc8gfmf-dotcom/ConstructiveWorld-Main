(* ==========================================================================)
   Arch_PA_03.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：rotc_supersedes_rot_id_set、rotc_supersedes_rot_wit_set、llm_rot_id_superseded_set、deprecated_Hsup_mono_set、deprecated_H_adj_cross_phase_lb_set、deprecated_u12_phase_side_set、dep_map_llm_Pmid_zero_set、deprecated_cluster_fully_covered、H_lam_anti_mono_real_set。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Require DTPT.
Require DTPT_Entropy.
Require DTPT_Rotation.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAttnGibbs.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import SecondLawQuantified.
From Stdlib Require Import Setoid Morphisms.

(* ================= §1 rotc_supersedes_rot_id_set 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
Import ListNotations.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Rotation.DTPT_Rotation.

Module DTPT_Bridge_Dep.

(* ========== §1 本地信息性类型族（QleT/QeqT 惯例副本） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Arguments qleT_intro {x y} _.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

Arguments qeqT_intro {x y} _.

(* ========== §2 保底件：supersession 信息性双/三件 ==========
   盘面（DTPT_Rotation.v §S10，只读依存）：
   - L2445 rotc_supersedes_rot_id : forall n l, rot n l = l
     （firstn_skipn 直证，不依存弃用件 llm_rot_id）；
   - L2456 llm_rot_id_superseded : forall n l P, P l <-> P (rot n l)
     （P 面迁移零损失）。 *)

(* ① 依存 ：rot n l = l 的 list 级直等 sumbool 判定面。
   恒等处置已证结论 ⇒ 判定恒归 Left（这就是处置的实质：旧 rot 名下
   恒等重写依存无条件由真化基础模块给出）；left 构造子携 Prop 证明参
   ＝提取擦除惯例，无 Prop 消除入 Type。 *)
Theorem rotc_supersedes_rot_id_set : forall (n : nat) (l : list Q),
  {rot n l = l} + {rot n l <> l}.
Proof.
  intros n l.
  left.
  apply rotc_supersedes_rot_id.
Defined.

(* ② 依存 ：list 级直等的 sigT 见证面——重构列表信息性入证书
   （w := l，逐字即处置定理的等式右端），非退化旋转下 rot n l 的
   实际表值可提取。 *)
Theorem rotc_supersedes_rot_wit_set : forall (n : nat) (l : list Q),
  {w : list Q & rot n l = w}.
Proof.
  intros n l.
  exists l.
  apply rotc_supersedes_rot_id.
Defined.

(* ③ 依存  llm_rot_id_superseded（P 面 P↔P∘rot 迁移零损失）
   在熵实例 P := fun m => H_adj m == H_adj l 的 QeqT 面：迁移定理
   proj1（P l -> P (rot n l)）吃 Qeq_refl 一步——恒等重写在熵面
   零损失的信息性证书（P 面择熵面＝恒等簇依存主力，规格文件 QeqT
   面授权）。 *)
Theorem llm_rot_id_superseded_set : forall (n : nat) (l : list Q),
  QeqT (H_adj (rot n l)) (H_adj l).
Proof.
  intros n l.
  apply qeqT_intro.
  apply (proj1 (llm_rot_id_superseded n l                  (fun m : list Q => (H_adj m == H_adj l)%Q))).
  apply Qeq_refl.
Defined.

(* ========== §3 主件：八件映射逐件抽样 Set 面（3 件代表作：
   映射④ Hsup_mono / 映射⑦ H_adj_cross_phase_lb /
   映射⑧ u12_phase_side_always_zero 各一） ==========
   共同纪律：旧面性质经真化层重述，依存 CLN-1 映射定理 + 真化层
   现役件，禁重证。 *)

(* ④ 依存  deprecated_consumers_map_Hsup_mono（映射④：
   旧面 Hsup l n <= Hsup l (S n) 经 helper Hsup_oldface_const
   （L2502 旧 Hsup 面恒常值 = H_adj l，X1 结论定理化）+ 真化面
   Hsup_cyc_mono 同形在册的双覆盖）旧面分量的 QleT 信息性面。 *)
Theorem deprecated_Hsup_mono_set : forall (l : list Q) (n : nat),
  QleT (Hsup l n) (Hsup l (S n)).
Proof.
  intros l n.
  apply qleT_intro.
  exact (proj1 (deprecated_consumers_map_Hsup_mono l n)).
Defined.

(* ⑤ 依存  deprecated_consumers_map_H_adj_cross_phase_lb
   （映射⑦：旧跨相下界 H_adj (P0 l) <= H_adj (Pinf l s) 经
   Pinf_true_id + H_adj_P0_min（Entropy:428 现役）重推；真化面
   phcyc_min_perm + rotc_perm 覆盖任意 k 含 Pinf_c——同时是 §S7
   两处重定向的基础模块）三分量的 QleT Type 积面（旧面 + 任意 k 真旋转
   面 + Pinf_c 面，逐件照盘三分信息性无损迁移）。 *)
Theorem deprecated_H_adj_cross_phase_lb_set :
  forall (l : list Q) (s k : nat),
  (QleT (H_adj (P0 l)) (H_adj (Pinf l s)) *
   (QleT (H_adj (P0 l)) (H_adj (rotc k l)) *
   QleT (H_adj (P0 l)) (H_adj (Pinf_c l s))))%type.
Proof.
  intros l s k. split.
  - apply qleT_intro.
    exact (proj1 (deprecated_consumers_map_H_adj_cross_phase_lb l s k)).
  - split.
    + apply qleT_intro.
      exact (proj1 (proj2 (deprecated_consumers_map_H_adj_cross_phase_lb
                             l s k))).
    + apply qleT_intro.
      exact (proj2 (proj2 (deprecated_consumers_map_H_adj_cross_phase_lb
                             l s k))).
Defined.

(* ⑥ 依存  deprecated_consumers_map_u12_phase_side_always_zero
   （映射⑧：旧判别器 phase_side l s = 0%nat 经定义展开 + Pinf_true_id
   + xq_Qle_bool_true + H_adj_P0_min 绕行弃用名重推；真化面
   phase_side_cyc_side_zero 在册）的信息性双证书面：判别值 sigT
   见证（v := 0，判别器输出信息性入证书）+ rotc 口径判别支路
   QleT（H_adj (P0 l) <= H_adj (rotc s l)，支路取 0 分支的信息性
   根由——依存映射⑦任意 k 面在 k := s 的实例）。 *)
Theorem deprecated_u12_phase_side_set : forall (l : list Q) (s : nat),
  ({v : nat & phase_side l s = v} *
   QleT (H_adj (P0 l)) (H_adj (rotc s l)))%type.
Proof.
  intros l s. split.
  - exists 0%nat.
    exact (proj1 (deprecated_consumers_map_u12_phase_side_always_zero
                    l s)).
  - apply qleT_intro.
    exact (proj1 (proj2 (deprecated_consumers_map_H_adj_cross_phase_lb
                           l s s))).
Defined.

(* ========== §4 主件：处置完备性（八件映射联合覆盖证书） ==========
   deprecated_cluster_fully_covered：真化层对恒等簇全部依存场景的
   覆盖证书——八件映射逐件 Set 形分量联合配对（信息性合取）。
   覆盖核验（弃用件 → 本证书分量）：
   ① D5_Pinf_perm（L2515）→ 分量1+2：内容等式面强于置换面
     （Pinf l s = w 且 w = l ⇒ Permutation 经 rotc_supersedes… 基础模块
     平凡成立；Pinf_c 面同理由分量2 等式给出，Permutation l
     (Pinf_c l s) 由映射⑥第三分量在册）；
   ② llm_Pmid_zero（L2529）→ 分量3：内容面（Pmid l s 0 = l）+
     熵面 QeqT 双证书；
   ③ P0_absorbs_Pmid（L2547）→ 分量4：全 k 吸收见证面（sorted
     卫哨诚实代价照录，§S8 F2b 结论在案）；
   ④ Hsup_mono（L2559）→ 分量5（= 主④）；
   ⑤ Hsup_bounded（L2572）→ 分量6+7：旧面 len#1·B·2 界（经
     H_adj_bound 同一基础模块绕行弃用名）+ 真化面 3·spread 界（诚实
     卫哨 SortedQ + l <> [] 随行）；
   ⑥ Pinf_eq_l（L2587）→ 分量1+2（旧名陈述由现役同形件零损失
     给出面 = Pinf l s = l；真化内容 Pinf_c l s = rotc (S s) l
     信息性携带具体旋转表）；
   ⑦ H_adj_cross_phase_lb（L2605）→ 分量8（= 主⑤ 三面全体）；
   ⑧ u12_phase_side_always_zero（L2625）→ 分量9（= 主⑥ 双证书）。
   8/8 全覆盖，零豁免。 *)

(* 逐件 helper（分量3 的独立可用形）：映射② 的内容+熵双证书。 *)
Theorem dep_map_llm_Pmid_zero_set : forall (l : list Q) (s : nat),
  ({w : list Q & Pmid l s 0%nat = w} *
   QeqT (H_adj (Pmid l s 0%nat)) (H_adj l))%type.
Proof.
  intros l s. split.
  - exists l. exact (proj1 (deprecated_consumers_map_llm_Pmid_zero l s)).
  - apply qeqT_intro.
    exact (proj2 (deprecated_consumers_map_llm_Pmid_zero l s)).
Defined.

(* 联合覆盖定理（九分量 Type 积；卫哨照盘映射③⑤原样随行）。 *)
Theorem deprecated_cluster_fully_covered :
  forall (l : list Q) (s k n : nat) (B : Q),
  (forall x : Q, In x l -> Qabs x <= B) -> SortedQ l -> l <> [] ->
  ({w : list Q & Pinf l s = w} *
  {w : list Q & Pinf_c l s = w} *
  ({w : list Q & Pmid l s 0%nat = w} *
   QeqT (H_adj (Pmid l s 0%nat)) (H_adj l)) *
  {w : list Q & P0 (Pmid l s k) = w} *
  QleT (Hsup l n) (Hsup l (S n)) *
  QleT (Hsup l n) (((Z.of_nat (length l) # 1)%Q * B * 2)%Q) *
  QleT (Hsup_cyc l n) ((3 * (lastq l - hd 0 l))%Q) *
  (QleT (H_adj (P0 l)) (H_adj (Pinf l s)) *
  (QleT (H_adj (P0 l)) (H_adj (rotc k l)) *
  QleT (H_adj (P0 l)) (H_adj (Pinf_c l s)))) *
  ({v : nat & phase_side l s = v} *
   QleT (H_adj (P0 l)) (H_adj (rotc s l))))%type.
Proof.
  intros l s k n B HB HS Hne.
  refine ((existT _ l (proj1 (deprecated_consumers_map_Pinf_eq_l l s)),
  existT _ (rotc (S s) l)
    (proj1 (proj2 (deprecated_consumers_map_Pinf_eq_l l s))),
  dep_map_llm_Pmid_zero_set l s,
  existT _ (P0 l)
    (deprecated_consumers_map_P0_absorbs_Pmid l s k HS),
  deprecated_Hsup_mono_set l n,
  qleT_intro (proj1 (deprecated_consumers_map_Hsup_bounded
                       l n B HB HS Hne)),
  qleT_intro (proj2 (deprecated_consumers_map_Hsup_bounded
                       l n B HB HS Hne)),
  deprecated_H_adj_cross_phase_lb_set l s k,
  deprecated_u12_phase_side_set l s)%type).
Defined.

(* ========== §5 加分件：§S10 依存面重定向示范双件的 Set 面 ========== *)

(* ⑦ 依存  H_lam_anti_mono_real（§S7  主同陈述重定向
   变体：斜率非正装配处经 Pinf_true_id + H_adj_P0_min 真化锚，
   弃用名零出现）的 QleT 面：λ-反单调性信息性证书。 *)
Theorem H_lam_anti_mono_real_set :
  forall (l : list Q) (s : nat) (lam1 lam2 : Q),
  (lam1 <= lam2)%Q -> QleT (H_lam l s lam2) (H_lam l s lam1).
Proof.
  intros l s lam1 lam2 Hlam.
  apply qleT_intro.
  exact (H_lam_anti_mono_real l s lam1 lam2 Hlam).
Defined.

(* ⑧ 依存  lam_opt_cross_phase_real（§S7  诚实锚同陈述
   变体：跨相下界经真化锚两步装配）的 QeqT 面：对齐选择器跨相
   恒取 1 的信息性证书。 *)
Theorem lam_opt_cross_phase_real_set : forall (l : list Q) (s : nat),
  QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) 1%Q.
Proof.
  intros l s. apply qeqT_intro.
  rewrite (lam_opt_cross_phase_real l s). apply Qeq_refl.
Defined.

(* ⑨ 同依存点的 sigT 见证面：选择器输出值信息性入证书
   （v := 1%Q）。Q 型 sigT 体的等式载体沿 B12 ⑧ 配方用 QeqT
   （Q 型 sigT 体裸 `=` 会被 Q_scope 侧解释吞成 Qeq，实测遇到问题；
   QeqT 载体同时是双信息性层：见证值 + Qeq 证书）。 *)
Theorem lam_opt_cross_phase_wit_set : forall (l : list Q) (s : nat),
  {v : Q & QeqT (lam_opt (H_adj (P0 l)) (H_adj (Pinf l s))) v}.
Proof.
  intros l s. exists 1%Q. apply qeqT_intro.
  rewrite (lam_opt_cross_phase_real l s). apply Qeq_refl.
Defined.

(* ---------- §6 提取检验（B14；b14_ 前缀，U12 配方：
     逐件独立提取，验收指标＝Obj.magic 计数 0，验后产物清除） ---------- *)

Set Extraction Output Directory ".".
Extraction "b14_rotc_supersedes_rot_id_set_ext.ml" rotc_supersedes_rot_id_set.
Extraction "b14_rotc_supersedes_rot_wit_set_ext.ml" rotc_supersedes_rot_wit_set.
Extraction "b14_llm_rot_id_superseded_set_ext.ml" llm_rot_id_superseded_set.
Extraction "b14_deprecated_Hsup_mono_set_ext.ml" deprecated_Hsup_mono_set.
Extraction "b14_deprecated_H_adj_cross_phase_lb_set_ext.ml" deprecated_H_adj_cross_phase_lb_set.
Extraction "b14_deprecated_u12_phase_side_set_ext.ml" deprecated_u12_phase_side_set.
Extraction "b14_dep_map_llm_Pmid_zero_set_ext.ml" dep_map_llm_Pmid_zero_set.
Extraction "b14_deprecated_cluster_fully_covered_ext.ml" deprecated_cluster_fully_covered.
Extraction "b14_H_lam_anti_mono_real_set_ext.ml" H_lam_anti_mono_real_set.
Extraction "b14_lam_opt_cross_phase_real_set_ext.ml" lam_opt_cross_phase_real_set.
Extraction "b14_lam_opt_cross_phase_wit_set_ext.ml" lam_opt_cross_phase_wit_set.

(* ---------- §7 终验：公理闭包审计（B14 新增 11 件，
     期望全 Closed） ---------- *)

Print Assumptions rotc_supersedes_rot_id_set.
Print Assumptions rotc_supersedes_rot_wit_set.
Print Assumptions llm_rot_id_superseded_set.
Print Assumptions deprecated_Hsup_mono_set.
Print Assumptions deprecated_H_adj_cross_phase_lb_set.
Print Assumptions deprecated_u12_phase_side_set.
Print Assumptions dep_map_llm_Pmid_zero_set.
Print Assumptions deprecated_cluster_fully_covered.
Print Assumptions H_lam_anti_mono_real_set.
Print Assumptions lam_opt_cross_phase_real_set.
Print Assumptions lam_opt_cross_phase_wit_set.

End DTPT_Bridge_Dep.

(* PA 追印段（ 核验副本件） *)
Print Assumptions DTPT_Bridge_Dep.H_lam_anti_mono_real_set.
Print Assumptions DTPT_Bridge_Dep.deprecated_Hsup_mono_set.
Print Assumptions DTPT_Bridge_Dep.llm_rot_id_superseded_set.
Print Assumptions DTPT_Bridge_Dep.rotc_supersedes_rot_wit_set.
Print Assumptions DTPT_Bridge_Dep.rotc_supersedes_rot_id_set.
(* ================= §2 uabS4_le_add_r 族 ================= *)
From Stdlib Require Import QArith.Qring.

(* §0 库内接口核对（Check 逐项对照真实签名）                            *)

Check real_le_b.              (* Bishop 形 ≤（可达最强形谓词，见 UpRealLeB） *)
Check real_le_closure_b_one.  (* 逐 eps 完成为 B 形（单步闭包） *)
Check real_le_closure_b.      (* 带加权正性证书 D 的 B 形闭合 *)
Check real_abs_triangle_le_B. (* |a+b| ≤_B |a|+|b|（B 形三角不等式） *)
Check real_abs_triangle_le_eps. (* |a+b| ≤ (|a|+|b|)+eps 逐 eps（两点核三角不等式） *)
Check real_lt_zero_one.       (* 0 < 1（W(nil) 正性证书） *)
Check real_lt_plus_r_zero.    (* y < y+eps（见 UpRealLeB） *)
Check real_list_sum.          (* list 折叠（X 全称，见 S08_RealMainlineDPO） *)
Check RealSetoid.real_eq_abs_compat. (* abs 尊重 real_eq *)
Check real_abs_zero_req.      (* |0| ≡ 0 *)
Check real_lt_irrefl.         (* 实数 < 的反自反（归谬的共同落点） *)

(* §1 基础引理：正余量右吸收 ＋ 差形两点三角不等式                     *)

(* 基础引理：le a b ＋ 0 < c ⟹ le a (b+c)（正余量右吸收）。
   构造：Or 两支分别 lt 传递（b < b+c 经 (b+0) 换形平移）
   ／eq 支运输后同链；统一经 real_lt_le_iff_req 左注入收束。 *)
Lemma uabS4_le_add_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le a (real_plus b c).
Proof.
  intros a b c Hab Hc.
  apply (RealSetoid.real_lt_le_iff_req a (real_plus b c)). apply inl.
  destruct Hab as [Hab | Hab].
  - apply (real_lt_trans a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
  - apply (RealSetoid.real_lt_id_l a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
Qed.

(* A.1 两点核差形（逐 eps，Or-inl）：|a−c| ≤ (|a−b|+|b−c|)+eps。
   构造：差恒等式 eq 链 (a−b)+(b−c) ≡ a−c（assoc×2＋opp＋zero 五步，
   逐项经 real_eq_plus_compat 运输），abs 尊重 eq 后两点核三角直接应用。 *)
Lemma uabS4_abs_diff_triangle_le_eps : forall a b c e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a (real_opp c)))
          (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                (real_abs (real_plus b (real_opp c)))) e).
Proof.
  intros a b c e He.
  assert (Hdiff : real_eq (real_plus (real_plus a (real_opp b))
                                     (real_plus b (real_opp c)))
                          (real_plus a (real_opp c))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) (real_plus b (real_opp c))) a
               (real_opp c)).
      + apply real_eq_refl.
      + eapply real_eq_trans.
        * apply real_plus_assoc.
        * eapply real_eq_trans.
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                          (real_opp c) real_zero (real_opp c)).
             ++ apply (real_eq_trans _ _ _ (real_plus_comm (real_opp b) b)).
                apply real_plus_opp.
             ++ apply real_eq_refl.
          -- apply (real_eq_trans _ _ _ (real_plus_comm real_zero (real_opp c))).
             apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l _ _ _
           (RealSetoid.real_eq_abs_compat _ _
              (real_eq_sym (real_plus (real_plus a (real_opp b))
                                      (real_plus b (real_opp c)))
                           (real_plus a (real_opp c)) Hdiff))).
  exact (real_abs_triangle_le_eps (real_plus a (real_opp b))
                                  (real_plus b (real_opp c)) e He).
Qed.

(* A.2 两点核差形（B 形，可达最强形）：|a−c| ≤_B |a−b|+|b−c|。 *)
Theorem uabS4_abs_diff_triangle_le_B : forall a b c : Real,
  real_le_b (real_abs (real_plus a (real_opp c)))
            (real_plus (real_abs (real_plus a (real_opp b)))
                       (real_abs (real_plus b (real_opp c)))).
Proof.
  intros a b c.
  apply real_le_closure_b_one.
  intros e He.
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* A.3 两点世界（S := bool）B 形实例：两点为 abs_sum_le 问题的最小
   非平凡世界，此处直接应用 real_abs_triangle_le_B。 *)
Theorem uabS4_abs_sum_le_B_pair : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (real_abs_triangle_le_B (f true) (f false)).
Qed.

(* §2 list 折叠形：权函数加权归纳 ＋ B 形闭合                          *)

(* 权函数：W(nil)=1，W(w::rest)=W(rest)+1（定义性尾权 +1）。
   误差分配：单点引入每步恰一整单位 e，尾段余量由 W(rest)·e 承担，
   合计 (W(rest)+1)·e ≡ W(cons)·e——该分配逐级精确成立。 *)
Fixpoint uabS4_wlen (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_one
  | w :: rest => real_plus (uabS4_wlen X rest) real_one
  end.

(* 权正性证书：0 < W(l)（归纳：1 > 0；W(rest) > 0 平移至 W(rest)+1）。 *)
Lemma uabS4_wlen_pos : forall (X : Type) (l : list X),
  real_lt real_zero (uabS4_wlen X l).
Proof.
  intros X l. induction l as [| w rest IH].
  - exact real_lt_zero_one.
  - apply (real_lt_trans real_zero (uabS4_wlen X rest)
             (real_plus (uabS4_wlen X rest) real_one)).
    + exact IH.
    + apply real_lt_plus_r_zero. exact real_lt_zero_one.
Qed.

(* 归纳步引理（折叠归纳的 cons 一步）：
   两点核三角（单点引入，余量恰一整单位 e）＋尾段余量（w·e 加权承担）
   ⟹ 折叠目标余量 (w+1)·e。
   构造：经 real_le_plus_compat 合成，再以 assoc×3＋distrib/mult_one
   的 eq 链终运输（(w+1)·e ≡ w·e + e，经 comm/distrib 逐步重排）。 *)
Lemma uabS4_cons_glue : forall a s t w e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) (real_abs s)) e) ->
  real_le (real_abs s) (real_plus t (real_mult w e)) ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) t)
                     (real_mult (real_plus w real_one) e)).
Proof.
  intros a s t w e He Hpair Hih.
  assert (Hmid : real_le (real_plus (real_abs a) (real_abs s))
                         (real_plus (real_abs a) (real_plus t (real_mult w e)))).
  { apply (real_le_plus_compat (real_abs a) (real_abs a)
             (real_abs s) (real_plus t (real_mult w e))).
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl (real_abs a))).
    - exact Hih. }
  assert (Hstep : real_le (real_plus (real_plus (real_abs a) (real_abs s)) e)
                          (real_plus (real_plus (real_abs a)
                                     (real_plus t (real_mult w e))) e)).
  { apply (real_le_plus_compat _ _ e e).
    - exact Hmid.
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl e)). }
  assert (Hchain : real_le (real_abs (real_plus a s))
                           (real_plus (real_plus (real_abs a)
                                      (real_plus t (real_mult w e))) e)).
  { apply (real_le_trans _ _ _ Hpair Hstep). }
  apply (RealSetoid.real_le_id_r (real_abs (real_plus a s))
           (real_plus (real_plus (real_abs a) (real_plus t (real_mult w e))) e)
           (real_plus (real_plus (real_abs a) t)
                      (real_mult (real_plus w real_one) e))).
  - eapply real_eq_trans.
    + apply real_eq_sym. apply real_plus_assoc.
    + eapply real_eq_trans.
      * apply (RealSetoid.real_eq_plus_compat (real_abs a)
                   (real_plus (real_plus t (real_mult w e)) e) (real_abs a)
                   (real_plus t (real_plus (real_mult w e) e))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply real_plus_assoc.
      * eapply real_eq_trans.
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs a) t)
                        (real_plus (real_mult w e) e)
                        (real_plus (real_abs a) t)
                        (real_mult (real_plus w real_one) e)).
           ++ apply real_eq_refl.
           ++ apply real_eq_sym.
              apply (real_eq_trans _ _ _
                       (real_mult_comm (real_plus w real_one) e)).
              apply (real_eq_trans _ _ _ (real_distrib e w real_one)).
              apply (RealSetoid.real_eq_plus_compat (real_mult e w)
                          (real_mult e real_one) (real_mult w e) e).
              ** apply real_mult_comm.
              ** apply real_mult_one.
  - exact Hchain.
Qed.

(* B.1 加权归纳主体（逐 eps 形，权函数 W）：|Σ_l f| ≤ Σ_l|f| + W(l)·e。
   情形 l=[]：|0| ≡ 0 ≤ 0 + 1·e（正余量右吸收）；
   归纳步 l 到 w::rest：两点核三角以整单位 e 引入，尾段由归纳假设同权承担，经 uabS4_cons_glue 合成。 *)
Lemma uabS4_abs_list_sum_le_wt : forall (X : Type) (f : X -> Real) (l : list X)
                                        (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros X f l. induction l as [| w rest IH]; intro e; intro He.
  - apply (uabS4_le_add_r (real_abs (real_list_sum X f nil)) real_zero
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero).
      * exact real_abs_zero_req.
      * exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - apply (uabS4_cons_glue (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x => real_abs (f x)) rest)
             (uabS4_wlen X rest) e He).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest) e He).
    + exact (IH e He).
Qed.

(* B.2 B 形闭合（可达最强形）：|Σ_l f| ≤_B Σ_l|f|。
   real_le_closure_b 以 D := W(l) 显式正性证书闭合加权族。 *)
Theorem uabS4_abs_list_sum_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  apply (real_le_closure_b _ _ (uabS4_wlen X l) (uabS4_wlen_pos X l)).
  intros e He.
  exact (uabS4_abs_list_sum_le_wt X f l e He).
Qed.

(* B.3 逐 eps 形推论：B 形 ⟹ |Σ_l f| ≤ Σ_l|f| + eps（Or-inl 注入）。
   对照结论：B 形严格强于逐 eps 形——real_le_closure_b_one 即单步反演。 *)
Theorem uabS4_abs_list_sum_le_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                           (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (RealSetoid.real_lt_le_iff_req _ _).
  apply inl.
  exact (uabS4_abs_list_sum_le_B X f l e He).
Qed.

(* §3 余量倍率 2 的不可共存引理                                        *)

(* C.1 余量倍率 2 不可共存：0 < e ＋ real_lt (Y+2e) X ＋ real_le X (Y+e)
   不可能共存。构造：Or 两支都导出 real_lt (Y+2e) (Y+e)——
   lt 支经传递（Y+2e < X < Y+e）；eq 支经 RHS 运输（X ≡ Y+e）；
   另一侧 e < 2e 经平移给出 Y+e < Y+2e，与上式合取即与 real_lt_irrefl 矛盾。
   边界注记：余量恰为 e（倍率 1）时 eq 支与反向
   strict 可共存（xₙ−yₙ = e+1/n 型逼近例），倍率 2 方不可共存。 *)
Theorem uabS4_lt_double_margin_le_half_contr : forall X Y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus Y (real_plus e e)) X ->
  real_le X (real_plus Y e) ->
  Empty_set.
Proof.
  intros X Y e He Hfar Hle.
  assert (Hboom : real_lt (real_plus Y (real_plus e e))
                          (real_plus Y e) -> Empty_set).
  { intro Hbad.
    assert (Hfwd : real_lt (real_plus Y e) (real_plus Y (real_plus e e))).
    { apply (real_lt_plus_translate Y e (real_plus e e)).
      apply (RealSetoid.real_lt_id_l e (real_plus e real_zero) (real_plus e e)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate e real_zero e). exact He. }
    exact (real_lt_irrefl _ (real_lt_trans _ _ _ Hbad Hfwd)). }
  unfold real_le in Hle. destruct Hle as [Hlt | Heq].
  - exact (Hboom (real_lt_trans _ _ _ Hfar Hlt)).
  - apply Hboom.
    exact (RealSetoid.real_lt_id_r (real_plus Y (real_plus e e)) X
             (real_plus Y e) Heq Hfar).
Qed.

(* C.2 倍率 2 矛盾的差形实例（两点核差形与 C.1 的对角组合）：以逐 eps
   差形两点核（uabS4_abs_diff_triangle_le_eps）为 le 来源：real_lt (b + 2e) a ＋ |a−c| ≤_B |a−b|+|b−c| 型
   余量约束下的矛盾实例——B 形在 eps := e 处给出 le a (|a−b|+|b−c|+e)，
   代入 C.1 即得。 *)
Theorem uabS4_diff_double_kill : forall a b c e : Real,
  real_lt real_zero e ->
  real_lt (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                  (real_abs (real_plus b (real_opp c))))
                     (real_plus e e))
          (real_abs (real_plus a (real_opp c))) ->
  Empty_set.
Proof.
  intros a b c e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr           (real_abs (real_plus a (real_opp c)))           (real_plus (real_abs (real_plus a (real_opp b)))                      (real_abs (real_plus b (real_opp c)))) e He Hfar).
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设）         *)

Print Assumptions uabS4_le_add_r.
Print Assumptions uabS4_abs_diff_triangle_le_eps.
Print Assumptions uabS4_abs_diff_triangle_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_wlen_pos.
Print Assumptions uabS4_cons_glue.
Print Assumptions uabS4_abs_list_sum_le_wt.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_lt_double_margin_le_half_contr.
Print Assumptions uabS4_diff_double_kill.

(* PA 追印段（ 核验副本件） *)
Print Assumptions uabS4_diff_double_kill.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_abs_diff_triangle_le_B.
(* ================= §3 tsi_le_plus_eps_r 族 ================= *)
Import RealInterfaceEnhancedMod.

(* 装配桥 B1 辅件：eps 伸张一步引理（le a (a+eps)，0<eps）                 *)
Lemma tsi_le_plus_eps_r :
  forall (RI : RealInterfaceEnhanced) (a eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI a eps).
Proof.
  intros RI a eps Hlt.
  apply (@S01_BaseRing.le_id_l RI a
           (@S01_BaseRing.plus RI a (@S01_BaseRing.zero RI))
           (@S01_BaseRing.plus RI a eps)).
  - exact (id_sym (@S01_BaseRing.plus_zero RI a)).
  - exact (@S01_BaseRing.le_plus_compat RI a a (@S01_BaseRing.zero RI) eps
             (@S01_BaseRing.le_refl RI a)
             (@S01_BaseRing.lt_le_iff RI (@S01_BaseRing.zero RI) eps (inl Hlt))).
Qed.

(* 装配桥 B1：RI → RealInterfaceEnhancedSetoid (@R RI) 总实例（req:=Id）  *)
(*   76 字段直引 + 13 逐 eps 形字段经 tsi_le_plus_eps_r + le_trans。      *)
Instance tsi_rie_setoid (RI : RealInterfaceEnhanced)
  : RealInterfaceEnhancedSetoid (@S01_BaseRing.R RI)
  := Build_RealInterfaceEnhancedSetoid (@S01_BaseRing.R RI)
  (* setoid 核心：req := Id（S01 Set 层幺等） *)
  (fun x y => Id x y)
  (fun x => @id_refl _ x)
  (fun x y p => @id_sym _ x y p)
  (fun x y z p q => @id_trans _ x y z p q)
  (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI)
  (@S01_BaseRing.plus RI) (@S01_BaseRing.mult RI) (@S01_BaseRing.opp RI)
  (@S01_BaseRing.abs RI) (@S01_BaseRing.lt RI) (@S01_BaseRing.le RI)
  (fun x1 x2 y1 y2 p q => @id_cong2 _ _ _ (@S01_BaseRing.plus RI) x1 x2 y1 y2 p q)
  (fun x1 x2 y1 y2 p q => @id_cong2 _ _ _ (@S01_BaseRing.mult RI) x1 x2 y1 y2 p q)
  (fun x y p => @id_cong _ _ (@S01_BaseRing.opp RI) x y p)
  (fun x y p => @id_cong _ _ (@S01_BaseRing.abs RI) x y p)
  (fun x1 x2 y1 y2 p q h =>
     @S01_BaseRing.lt_id_r RI x2 y1 y2 q (@S01_BaseRing.lt_id_l RI x2 x1 y1 (id_sym p) h))
  (fun x1 x2 y1 y2 p q h =>
     @S01_BaseRing.le_id_r RI x2 y1 y2 q (@S01_BaseRing.le_id_l RI x2 x1 y1 (id_sym p) h))
  (* 环代数（Id 形 = req 形逐字同） *)
  (@S01_BaseRing.plus_assoc RI) (@S01_BaseRing.plus_comm RI)
  (@S01_BaseRing.plus_zero RI) (@S01_BaseRing.plus_opp RI)
  (@S01_BaseRing.mult_assoc RI) (@S01_BaseRing.mult_comm RI)
  (@S01_BaseRing.mult_one RI) (@S01_BaseRing.distrib RI)
  (@S01_BaseRing.mult_zero RI)
  (@S01_BaseRing.lt_irrefl RI) (@S01_BaseRing.lt_trans RI)
  (@S01_BaseRing.le_refl RI) (@S01_BaseRing.le_trans RI)
  (@S01_BaseRing.le_antisym RI) (@S01_BaseRing.le_lt_trans RI)
  (@S01_BaseRing.lt_le_trans RI) (@S01_BaseRing.lt_le_iff RI)
  (@S01_BaseRing.le_id_l RI) (@S01_BaseRing.le_id_r RI)
  (@S01_BaseRing.lt_id_l RI) (@S01_BaseRing.lt_id_r RI)
  (@S01_BaseRing.inv_pos RI) (@S01_BaseRing.inv_pos_correct RI)
  (@S01_BaseRing.one_pos RI)
  (@S01_BaseRing.lt_plus_compat RI) (@S01_BaseRing.le_plus_compat RI)
  (@S01_BaseRing.plus_positive RI) (@S01_BaseRing.mult_positive RI)
  (@S01_BaseRing.lt_mult_compat RI) (@S01_BaseRing.le_mult_compat RI)
  (@S01_BaseRing.le_mult_compat_weak RI) (@S01_BaseRing.opp_lt_compat RI)
  (@S01_BaseRing.lt_zero_opp RI) (@S01_BaseRing.opp_le_compat RI)
  (@S01_BaseRing.inv_pos_pos RI) (@S01_BaseRing.inv_pos_ext RI)
  (@S01_BaseRing.inv_pos_le_compat RI)
  (* min：逐 eps 形 = 非 eps 字段 + eps 伸张 *)
  (@S01_BaseRing.min RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.min RI a b) a
       (@S01_BaseRing.plus RI a eps)
       (@S01_BaseRing.min_le_l RI a b) (tsi_le_plus_eps_r RI a eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.min RI a b) b
       (@S01_BaseRing.plus RI b eps)
       (@S01_BaseRing.min_le_r RI a b) (tsi_le_plus_eps_r RI b eps Heps))
  (@S01_BaseRing.min_pos RI)
  (* r_max：逐 eps 形同款 *)
  (@S01_BaseRing.r_max RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI a (@S01_BaseRing.r_max RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.r_max RI a b) eps)
       (@S01_BaseRing.r_max_le_l RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.r_max RI a b) eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI b (@S01_BaseRing.r_max RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.r_max RI a b) eps)
       (@S01_BaseRing.r_max_le_r RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.r_max RI a b) eps Heps))
  (@S01_BaseRing.r_max_l_iff RI) (@S01_BaseRing.r_max_r_iff RI)
  (@S01_BaseRing.pos_test RI) (@S01_BaseRing.pos_test_lt RI)
  (@S01_BaseRing.lt_pos_test RI)
  (@S01_BaseRing.pos_part RI) (@S01_BaseRing.pos_part_def RI)
  (fun a eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.pos_part RI a)
       (@S01_BaseRing.plus RI (@S01_BaseRing.pos_part RI a) eps)
       (@S01_BaseRing.pos_part_nonneg RI a)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.pos_part RI a) eps Heps))
  (@S01_BaseRing.r_if RI) (@S01_BaseRing.r_if_true RI) (@S01_BaseRing.r_if_false RI)
  (* abs：逐 eps 形同款 *)
  (fun a eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.abs RI a)
       (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) eps)
       (@S01_BaseRing.abs_nonneg RI a)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.abs RI a) eps Heps))
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.abs RI (@S01_BaseRing.plus RI a b))
       (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b)) eps)
       (@S01_BaseRing.abs_triangle RI a b)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.abs RI a) (@S01_BaseRing.abs RI b))
          eps Heps))
  (@S01_BaseRing.abs_zero RI) (@S01_BaseRing.abs_mult RI)
  (@S01_BaseRing.abs_opp RI) (@S01_BaseRing.abs_pos RI)
  (@S01_BaseRing.exp_neg RI) (@S01_BaseRing.exp_neg_pos RI)
  (@S01_BaseRing.exp_neg_zero RI) (@S01_BaseRing.exp_neg_plus RI)
  (@S01_BaseRing.exp_neg_decr RI) (@S01_BaseRing.exp_neg_le_decr RI)
  (* log 家：受体 log:R->R 丢弃正性指标；log_le_linear_eps 源 = Enhanced *)
  (*   log_le_linear 字段（le (log x) (x-1)，minus := plus x (opp one) δ） *)
  (fun x _ => @S01_BaseRing.log RI x)
  (fun a b Ha Hb => @S01_BaseRing.log_mult RI a b Ha Hb)
  (fun _ => @S01_BaseRing.log_one RI)
  (fun x Hx eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.log RI x)
       (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI)))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI))) eps)
       (@S01_BaseRing.log_le_linear RI x Hx)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI x (@S01_BaseRing.opp RI (@S01_BaseRing.one RI)))
          eps Heps))
  (fun x _ => @S01_BaseRing.log_inv RI x)
  (fun x Hx => @S01_BaseRing.log_inv_log RI x Hx)
  (fun x _ => @S01_BaseRing.exp_neg_log_inv RI x)
  (* metric/lim/cauchy：逐 eps 形同款 + Id 形直引 *)
  (@S01_BaseRing.metric RI) (@S01_BaseRing.metric_sym RI)
  (fun a b eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.zero RI) (@S01_BaseRing.metric RI a b)
       (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b) eps)
       (@S01_BaseRing.metric_pos RI a b)
       (tsi_le_plus_eps_r RI (@S01_BaseRing.metric RI a b) eps Heps))
  (@S01_BaseRing.metric_zero RI)
  (fun a b c eps Heps =>
     @S01_BaseRing.le_trans RI (@S01_BaseRing.metric RI a c)
       (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b) (@S01_BaseRing.metric RI b c))
       (@S01_BaseRing.plus RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b)
             (@S01_BaseRing.metric RI b c)) eps)
       (@S01_BaseRing.metric_triangle RI a b c)
       (tsi_le_plus_eps_r RI
          (@S01_BaseRing.plus RI (@S01_BaseRing.metric RI a b)
             (@S01_BaseRing.metric RI b c)) eps Heps))
  (@S01_BaseRing.lim RI) (@S01_BaseRing.lim_unique RI)
  (@S01_BaseRing.cauchy_complete RI).

(* 装配桥 B2：受体定义出节 arity 桥（δ 闭合）                              *)
Theorem tsi_twp_is_boltzmann_weight :
  forall (RI : RealInterfaceEnhanced) (Token : Set)
         (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI)
         (t : @S01_BaseRing.R RI)
         (Ht : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) t)
         (prefix : list Token) (w : Token),
    Id (@temperature_weighted_prob RI Token neg_log_prob t Ht prefix w)
       (@S01_BaseRing.exp_neg RI
          (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht)
             (neg_log_prob prefix w))).
Proof. intros RI Token neg_log_prob t Ht prefix w. exact (@id_refl _ _). Qed.

(* 主件节：受体 LanguageModelExtensions 节面（RI Token neg_log_prob        *)
(*   temperature temperature_pos）⊕ 供体 ReqAttnGibbs 节求和机器槽。      *)
Section TsiMains.
Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI.
Variable temperature : @S01_BaseRing.R RI.
Variable temperature_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) temperature.

(* 求和机器诚实槽（供体节同款；BoltzmannBridgeDischarge 供给槽先例） *)
Variable sumf : (Token -> @S01_BaseRing.R RI) -> @S01_BaseRing.R RI.
Hypothesis Hsum_ext :
  forall f g : Token -> @S01_BaseRing.R RI,
    (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Hypothesis Hsum_linear :
  forall (a : @S01_BaseRing.R RI) (f : Token -> @S01_BaseRing.R RI),
    req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Hypothesis Hsum_add :
  forall f g : Token -> @S01_BaseRing.R RI,
    req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Hypothesis Hsum_pos :
  forall f : Token -> @S01_BaseRing.R RI,
    (forall w : Token, lt zero (f w)) -> lt zero (sumf f).

(*   （供体 ag_softmax_temp_normalized@262 全参实例化；z := nlp prefix·） *)
Theorem tsi_temp_weighted_normalized :
  forall prefix : list Token,
    req (sumf (fun w : Token =>
           mult (@temperature_weighted_prob RI Token neg_log_prob
                   temperature temperature_pos prefix w)
                (inv_pos
                   (sumf (fun w0 : Token =>
                            @temperature_weighted_prob RI Token neg_log_prob
                              temperature temperature_pos prefix w0))
                   (Hsum_pos
                      (fun w0 : Token =>
                         @temperature_weighted_prob RI Token neg_log_prob
                           temperature temperature_pos prefix w0)
                      (fun w0 : Token =>
                         @S01_BaseRing.exp_neg_pos RI
                           (@S01_BaseRing.mult RI
                              (@S01_BaseRing.inv_pos RI temperature temperature_pos)
                              (neg_log_prob prefix w0)))))))
        one.
Proof.
  intro prefix.
  exact (@ag_softmax_temp_normalized (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_ext Hsum_linear Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob prefix w)).
Qed.

(*   仍归一（供体 ag_softmax_temp_mix_normalized@282 全参实例化）         *)
Theorem tsi_temp_weighted_mix_normalized :
  forall (p q : list Token) (alpha : @S01_BaseRing.R RI),
    lt zero alpha -> lt zero (req_minus one alpha) ->
    req (sumf (fun w : Token =>
           plus (mult alpha
                      (mult (@temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos p w)
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        @temperature_weighted_prob RI Token
                                          neg_log_prob temperature temperature_pos
                                          p w0))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     @temperature_weighted_prob RI Token
                                       neg_log_prob temperature temperature_pos
                                       p w0)
                                  (fun w0 : Token =>
                                     @S01_BaseRing.exp_neg_pos RI
                                       (@S01_BaseRing.mult RI
                                          (@S01_BaseRing.inv_pos RI temperature
                                             temperature_pos)
                                          (neg_log_prob p w0)))))))
                (mult (req_minus one alpha)
                      (mult (@temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos q w)
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        @temperature_weighted_prob RI Token
                                          neg_log_prob temperature temperature_pos
                                          q w0))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     @temperature_weighted_prob RI Token
                                       neg_log_prob temperature temperature_pos
                                       q w0)
                                  (fun w0 : Token =>
                                     @S01_BaseRing.exp_neg_pos RI
                                       (@S01_BaseRing.mult RI
                                          (@S01_BaseRing.inv_pos RI temperature
                                             temperature_pos)
                                          (neg_log_prob q w0)))))))))
        one.
Proof.
  intros p q alpha Halpha Halpha1.
  exact (@ag_softmax_temp_mix_normalized (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_ext Hsum_linear Hsum_add Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob p w)           (fun w : Token => neg_log_prob q w)           alpha Halpha Halpha1).
Qed.

(*   1/c 尺度 softmax（供体 ag_temp_is_scale_duality@477 全参实例化；     *)
(*   LHS = 受体定义在温度 c 处（inv_pos c Hc 即进入指数），对偶不过深、   *)
(*   不砍）                                                               *)
Theorem tsi_temp_scale_duality :
  forall (c : @S01_BaseRing.R RI) (Hc : lt zero c)
         (prefix : list Token) (w : Token),
    req (mult (@temperature_weighted_prob RI Token neg_log_prob c Hc prefix w)
              (inv_pos
                 (sumf (fun w0 : Token =>
                          @temperature_weighted_prob RI Token neg_log_prob
                            c Hc prefix w0))
                 (Hsum_pos
                    (fun w0 : Token =>
                       @temperature_weighted_prob RI Token neg_log_prob
                         c Hc prefix w0)
                    (fun w0 : Token =>
                       @S01_BaseRing.exp_neg_pos RI
                         (@S01_BaseRing.mult RI
                            (@S01_BaseRing.inv_pos RI c Hc)
                            (neg_log_prob prefix w0))))))
        (reqd_softmax_scaled Token sumf Hsum_pos (inv_pos c Hc)
           (fun w1 : Token => neg_log_prob prefix w1) w).
Proof.
  intros c Hc prefix w.
  exact (@ag_temp_is_scale_duality (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_pos c Hc           (fun w1 : Token => neg_log_prob prefix w1) w).
Qed.

(*   （供体 ag_softmax_temp_relative@341 全参实例化；exp 加法同态真证面） *)
Theorem tsi_temp_weighted_relative :
  forall (prefix : list Token) (w w' : Token),
    req (mult (@temperature_weighted_prob RI Token neg_log_prob
                   temperature temperature_pos prefix w)
              (inv_pos
                 (sumf (fun w0 : Token =>
                          @temperature_weighted_prob RI Token neg_log_prob
                            temperature temperature_pos prefix w0))
                 (Hsum_pos
                    (fun w0 : Token =>
                       @temperature_weighted_prob RI Token neg_log_prob
                         temperature temperature_pos prefix w0)
                    (fun w0 : Token =>
                       @S01_BaseRing.exp_neg_pos RI
                         (@S01_BaseRing.mult RI
                            (@S01_BaseRing.inv_pos RI temperature temperature_pos)
                            (neg_log_prob prefix w0))))))
        (mult (mult (@temperature_weighted_prob RI Token neg_log_prob
                       temperature temperature_pos prefix w')
                    (inv_pos
                       (sumf (fun w0 : Token =>
                                @temperature_weighted_prob RI Token neg_log_prob
                                  temperature temperature_pos prefix w0))
                       (Hsum_pos
                          (fun w0 : Token =>
                             @temperature_weighted_prob RI Token neg_log_prob
                               temperature temperature_pos prefix w0)
                          (fun w0 : Token =>
                             @S01_BaseRing.exp_neg_pos RI
                               (@S01_BaseRing.mult RI
                                  (@S01_BaseRing.inv_pos RI temperature
                                     temperature_pos)
                                  (neg_log_prob prefix w0))))))
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (neg_log_prob prefix w)
                                        (neg_log_prob prefix w'))))).
Proof.
  intros prefix w w'.
  exact (@ag_softmax_temp_relative (@S01_BaseRing.R RI) (tsi_rie_setoid RI)           Token sumf Hsum_pos temperature temperature_pos           (fun w1 : Token => neg_log_prob prefix w1) w w').
Qed.

End TsiMains.

(* G4 审查留痕面（Print Assumptions ≥1 达标：5 处）                        *)
Print Assumptions tsi_twp_is_boltzmann_weight.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_relative.

Print Assumptions tsi_temp_weighted_relative.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_rie_setoid.
(* ================= §4 slc_minus_r_plus_cancel 族 ================= *)
(* ---------------------------------------------------------- *)
(* 件 0：Set 层带状对（双边定量语句面；set 层 inductive，零 Prop）  *)
(* ---------------------------------------------------------- *)
Inductive slc_band (A B : Set) : Set :=
| slc_band_intro : A -> B -> slc_band A B.

(* ---------------------------------------------------------- *)
(* 件 1–3：real 算术 choreography 三辅助引理（全 real_eq 档）        *)
(*   (a−b)+b == a ／ (a+b)+(−b) == a ＋ (x+y)+(−z) == (x+(−z))+y  *)
(* ---------------------------------------------------------- *)
Lemma slc_minus_r_plus_cancel :
  forall a b : Real,
    real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_minus_r a b) b)           (real_plus a (real_plus (real_opp b) b))           a           (real_eq_sym (real_plus a (real_plus (real_opp b) b))                        (real_plus (real_plus a (real_opp b)) b)                        (real_plus_assoc a (real_opp b) b))           (real_eq_trans              (real_plus a (real_plus (real_opp b) b))              (real_plus a (real_plus b (real_opp b)))              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus (real_opp b) b) (real_plus b (real_opp b))                 (real_eq_refl a) (real_plus_comm (real_opp b) b))              (real_eq_trans                 (real_plus a (real_plus b (real_opp b)))                 (real_plus a real_zero)                 a                 (RealSetoid.real_eq_plus_compat_adapt a a                    (real_plus b (real_opp b)) real_zero                    (real_eq_refl a) (real_plus_opp b))                 (real_plus_zero a)))).
Qed.

Lemma slc_plus_r_assoc_cancel :
  forall a b : Real,
    real_eq (real_plus (real_plus a b) (real_opp b)) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_plus a b) (real_opp b))           (real_plus a (real_plus b (real_opp b)))           a           (real_eq_sym (real_plus a (real_plus b (real_opp b)))                        (real_plus (real_plus a b) (real_opp b))                        (real_plus_assoc a b (real_opp b)))           (real_eq_trans              (real_plus a (real_plus b (real_opp b)))              (real_plus a real_zero)              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus b (real_opp b)) real_zero                 (real_eq_refl a) (real_plus_opp b))              (real_plus_zero a))).
Qed.

Lemma slc_plus_comm_r_shift :
  forall x y z : Real,
    real_eq (real_plus (real_plus x y) (real_opp z))
            (real_plus (real_plus x (real_opp z)) y).
Proof.
  intros x y z.
  exact (real_eq_trans           (real_plus (real_plus x y) (real_opp z))           (real_plus x (real_plus y (real_opp z)))           (real_plus (real_plus x (real_opp z)) y)           (real_eq_sym (real_plus x (real_plus y (real_opp z)))                        (real_plus (real_plus x y) (real_opp z))                        (real_plus_assoc x y (real_opp z)))           (real_eq_trans              (real_plus x (real_plus y (real_opp z)))              (real_plus x (real_plus (real_opp z) y))              (real_plus (real_plus x (real_opp z)) y)              (RealSetoid.real_eq_plus_compat_adapt x x                 (real_plus y (real_opp z)) (real_plus (real_opp z) y)                 (real_eq_refl x) (real_plus_comm y (real_opp z)))              (real_plus_assoc x (real_opp z) y))).
Qed.

(* 第一部分：任意和机器上的双边依存（Section 槽照 slq 同形同序）    *)

Section SlcSecondLawConsume.

Variable S : Type.
Variable sumf : (S -> Real) -> Real.
Hypothesis sumpos :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (sumf f).
Hypothesis sumext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sumlinear : forall (a : Real) (f : S -> Real),
  real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)).
Hypothesis sumadd : forall (f g : S -> Real),
  real_eq (sumf (fun s : S => real_plus (f s) (g s)))
          (real_plus (sumf f) (sumf g)).
Variable T : Real.
Hypothesis T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* 肢 1：KL ≤ 熵增 + eps（lower 之 plus 形；依存 slq_entropy_gain_kl_lower） *)
Lemma slc_kl_le_gain_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_lower S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hlow.
  exact (RealSetoid.real_le_id_r
           (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                       (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                         (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                          (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                            (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                               (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 Hlow
                 (real_le_refl (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* 肢 2：熵增 ≤ KL + eps（upper 之 plus 形；依存 slq_entropy_gain_kl_upper） *)
Lemma slc_gain_le_kl_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_upper S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hup.
  exact (RealSetoid.real_le_id_r
           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                       (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                         (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                          (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                            (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                               (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 Hup
                 (real_le_refl (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 1：per-eps 双边定量（Set 层带状对，下界+上界合并装配） *)
(*   |S[p_T] − S[p] − KL(p‖p_T)| 的逐 eps 带状读法：                *)
(*   KL ≤ 增 + eps 且 增 ≤ KL + eps。                                *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_kl_two_sided_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      slc_band
        (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))
        (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (slc_band_intro           (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))           (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps))           (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)           (slc_gain_le_kl_plus_leg p Hp Hnp Henergy eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 2：熵增益 ≥ KL 缺陷 − eps（显式依存形；回喂基座依存位）      *)
(*   real_le (KL − eps) 增——lower 的 minus-r 地板形。               *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_ge_kl_minus_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (RealSetoid.real_le_id_r           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) (real_opp eps))           (real_plus (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)                      (real_opp eps))           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)           (slc_plus_r_assoc_cancel (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)           (real_le_plus_compat              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)              (real_opp eps)              (real_opp eps)              (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)              (real_le_refl (real_opp eps)))).
Qed.

End SlcSecondLawConsume.

(* 第二部分：list 机器全闭双依存（核心定理 × eps_list 依存链）       *)

(* ---------------------------------------------------------- *)
(* 主件 3：均衡点 KL 归零——核心定理在 p := p_T 处实例化（全闭）      *)
(*   归一化（boltzmann_normalized）+ 同能量（E(p_T) == E_T 定义性）    *)
(*   ⟹ S[p_T] − S[p_T] == KL(p_T‖p_T) ⟹ KL(p_T‖p_T) == 0。          *)
(* ---------------------------------------------------------- *)
Theorem slc_kl_boltz_self_zero :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real),
    real_eq real_zero
      (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
            real_list_sum_pos X f l Hf Hnil)
         T Ht energy
         (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)
         (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)).
Proof.
  intros X l Hnil T Ht energy.
  set (SF := fun g : X -> Real => real_list_sum X g l).
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil).
  set (B := real_boltzmann_dist_temp X SF SP T Ht energy).
  set (Bp := real_boltzmann_dist_temp_pos X SF SP T Ht energy).
  set (SD := real_entropy_dist X SF B Bp).
  pose proof (real_entropy_deficit_kl_temp X SF SP
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy B Bp
                (real_boltzmann_dist_temp_normalized X SF SP
                   (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                   (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                   T Ht energy)
                (real_eq_refl
                   (real_energy_exp_temp X SF SP T Ht energy))) as Hdef.
  unfold real_minus_r in Hdef.
  exact (real_eq_sym
           (real_KL_temp X SF SP T Ht energy B Bp) real_zero
           (real_eq_trans
              (real_KL_temp X SF SP T Ht energy B Bp)
              (real_plus SD (real_opp SD))
              real_zero
              (real_eq_sym (real_plus SD (real_opp SD))
                           (real_KL_temp X SF SP T Ht energy B Bp)
                           Hdef)
              (real_plus_opp SD))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 4：Second Law eps 档 × 核心恒等式合流 ⟹ KL ≥ −eps            *)
(*   依存 slq_second_law_eps_list（S[p] ≤ S[p_T]+eps）与核心定理      *)
(*   （S[p_T]−S[p] == KL）双源：0 ≤ 增+eps 沿恒等式换载 ⟹ −eps ≤ KL。 *)
(* ---------------------------------------------------------- *)
Theorem slc_second_law_kl_floor_eps_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnp : real_eq (real_list_sum X p l) real_one)
         (Henergy : real_eq
                      (real_list_sum X (fun s : X => real_mult (p s) (energy s)) l)
                      (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_opp eps)
            (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  real_list_sum_pos X f l Hf Hnil)
               T Ht energy p Hp).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  pose proof (slq_second_law_eps_list X l Hnil T Ht energy p Hp Hnp Henergy eps Heps) as Hsl.
  pose proof (real_entropy_deficit_kl_temp X
                (fun g : X -> Real => real_list_sum X g l)
                (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                   real_list_sum_pos X f l Hf Hnil)
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy p Hp Hnp Henergy) as Hdef.
  set (SF := fun g : X -> Real => real_list_sum X g l) in *.
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil) in *.
  set (Sp := real_entropy_dist X SF p Hp) in *.
  set (Sb := real_entropy_dist X SF
               (real_boltzmann_dist_temp X SF SP T Ht energy)
               (real_boltzmann_dist_temp_pos X SF SP T Ht energy)) in *.
  set (K := real_KL_temp X SF SP T Ht energy p Hp) in *.
  (* 步 1：eps_list 加 −Sp ⟹ 0 ≤ (Sb+eps)+(−Sp) *)
  pose proof (RealSetoid.real_le_id_l real_zero
                (real_plus Sp (real_opp Sp))
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_eq_sym (real_plus Sp (real_opp Sp)) real_zero
                             (real_plus_opp Sp))
                (real_le_plus_compat Sp (real_plus Sb eps)
                 (real_opp Sp) (real_opp Sp)
                 Hsl (real_le_refl (real_opp Sp)))) as Hstep1.
  (* 步 2：换序 ⟹ 0 ≤ (Sb+(−Sp))+eps = 0 ≤ 增+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_plus (real_plus Sb (real_opp Sp)) eps)
                (slc_plus_comm_r_shift Sb eps Sp)
                Hstep1) as Hstep2.
  (* 步 3：沿核心恒等式 增 == KL 换载 ⟹ 0 ≤ KL+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_minus_r Sb Sp) eps)
                (real_plus K eps)
                (RealSetoid.real_eq_plus_compat_adapt (real_minus_r Sb Sp) K eps eps
                   Hdef (real_eq_refl eps))
                Hstep2) as Hstep3.
  (* 步 4：加 −eps ⟹ −eps ≤ (KL+eps)+(−eps) *)
  pose proof (real_le_plus_compat real_zero (real_plus K eps)
                 (real_opp eps) (real_opp eps)
                 Hstep3 (real_le_refl (real_opp eps))) as Hstep4.
  (* 步 5：归零闭合 ⟹ −eps ≤ KL *)
  exact (RealSetoid.real_le_id_r (real_opp eps)
           (real_plus (real_plus K eps) (real_opp eps))
           K
           (slc_plus_r_assoc_cancel K eps)
           (RealSetoid.real_le_id_l (real_opp eps)
              (real_plus real_zero (real_opp eps))
              (real_plus (real_plus K eps) (real_opp eps))
              (real_eq_sym (real_plus real_zero (real_opp eps)) (real_opp eps)
                 (real_eq_trans (real_plus real_zero (real_opp eps))
                                (real_plus (real_opp eps) real_zero)
                                (real_opp eps)
                                (real_plus_comm real_zero (real_opp eps))
                                (real_plus_zero (real_opp eps))))
              Hstep4)).
Qed.

(* 审查留痕：Print Assumptions（G4）                                       *)
Print Assumptions slc_gain_kl_two_sided_eps.
Print Assumptions slc_gain_ge_kl_minus_eps.
Print Assumptions slc_kl_boltz_self_zero.
Print Assumptions slc_second_law_kl_floor_eps_list.

(* PA 追印段（ 核验副本件） *)
Print Assumptions slc_gain_ge_kl_minus_eps.
Print Assumptions slc_gain_kl_two_sided_eps.
Print Assumptions slc_plus_comm_r_shift.
Print Assumptions slc_plus_r_assoc_cancel.
Print Assumptions slc_minus_r_plus_cancel.
(* ================= §5 QltT 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Lia QArith.Qminmax.

(* §0 Set 层出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 B4 §0） *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. apply (QltT_to_Qlt x y). exact H. Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  apply Qle_to_QleT'.
  apply (Qle_trans a b c H).
  apply qeq_le.
  exact Hbc.
Qed.

(* §1 序/等小桥：Qeq 运输、乘左单调、倒数反序、除法单调             *)

(* ---- Qeq 左端运输：x == y -> y < z -> x < z ---- *)
Lemma eoe_lt_eq_l : forall x y z : Q, x == y -> Qlt y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz.
  apply (Qle_lt_trans x y z).
  - apply qeq_le. exact Hxy.
  - exact Hyz.
Qed.

(* ---- Qeq 右端运输：x < y -> y == z -> x < z ---- *)
Lemma eoe_lt_eq_r : forall x y z : Q, Qlt x y -> y == z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz.
  apply (Qlt_le_trans x y z).
  - exact Hxy.
  - apply qeq_le. exact Hyz.
Qed.

(* ---- 乘左单调（Qmult_le_compat_r 的项序桥：u*v ≤ u*w） ---- *)
Lemma eoe_mult_le_l : forall u v w : Q, Qle v w -> Qle 0 u -> Qle (u * v) (u * w).
Proof.
  intros u v w Hvw Hu.
  apply (Qle_trans _ (v * u)).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (w * u)).
    + apply Qmult_le_compat_r.
      * exact Hvw.
      * exact Hu.
    + apply qeq_le. ring.
Qed.

(* ---- 倒数反序（Qle 形）：0 < x -> 0 < y -> y ≤ x -> /x ≤ /y ---- *)
Lemma eoe_qinv_le : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qle y x -> Qle (/ x) (/ y).
Proof.
  intros x y Hx Hy Hyx.
  destruct (Qle_lt_or_eq y x Hyx) as [Hlt | Heq].
  - apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar y x Hy Hx)). exact Hlt.
  - rewrite Heq. apply Qle_refl.
Qed.

(* ---- 除法单调（Qle 形）：同分子、正分母，大分母商更小 ---- *)
Lemma eoe_div_le : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qle z y -> Qle (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  assert (Hinv : Qle (/ y) (/ z)) by (apply (eoe_qinv_le y z); assumption).
  apply (Qle_trans _ (/ y * a)).
  - apply qeq_le. unfold Qdiv. ring.
  - apply (Qle_trans _ (/ z * a)).
    + apply Qmult_le_compat_r.
      * exact Hinv.
      * apply (Qlt_le_weak 0 a). exact Ha.
    + apply qeq_le. unfold Qdiv. ring.
Qed.

(* ---- 除法单调（Qlt 形）：严格版 ---- *)
Lemma eoe_div_lt : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qlt z y -> Qlt (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  assert (Hinv : Qlt (/ y) (/ z)).
  { apply (proj1 (Qinv_lt_contravar z y Hz Hy)). exact Hzy. }
  apply (eoe_lt_eq_l _ (/ y * a)).
  - unfold Qdiv. ring.
  - apply (eoe_lt_eq_r _ (/ z * a)).
    + apply (Qmult_lt_compat_r (/ y) (/ z) a).
      * exact Ha.
      * exact Hinv.
    + unfold Qdiv. ring.
Qed.

(* §2 阶乘序结构（支撑件 1：n! 单调正，≥ max(1, n)）               *)

Lemma eoe_fact_ge_one : forall k : nat, Qle (1%Q) (q_fact k).
Proof.
  induction k as [| k IH].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1))).
    + unfold Qle. simpl. lia.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * (1%Q))).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
        -- apply eoe_mult_le_l.
           ++ exact IH.
           ++ unfold Qle. simpl. lia.
        -- apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_ge_self : forall k : nat, Qle (Z.of_nat k # 1) (q_fact k).
Proof.
  intro k. destruct k as [| j].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * (1%Q))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      * apply eoe_mult_le_l.
        -- apply eoe_fact_ge_one.
        -- unfold Qle. simpl. lia.
      * apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_step_ge : forall k : nat, Qle (q_fact k) (q_fact (Datatypes.S k)).
Proof.
  intro k.
  apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
  - apply (Qle_trans _ (q_fact k * (Z.of_nat (Datatypes.S k) # 1))).
    + apply (Qle_trans _ (q_fact k * 1%Q)).
      * apply qeq_le. ring.
      * apply eoe_mult_le_l.
        -- unfold Qle. simpl. lia.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply q_fact_pos.
    + apply qeq_le. ring.
  - apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_mono_add : forall d a : nat, Qle (q_fact a) (q_fact (a + d)).
Proof.
  intros d a. induction d as [| d IH].
  - replace (a + 0)%nat with a by lia. apply Qle_refl.
  - replace (a + Datatypes.S d)%nat with (Datatypes.S (a + d)) by lia.
    apply (Qle_trans _ (q_fact (a + d))).
    + exact IH.
    + apply eoe_fact_step_ge.
Qed.

Lemma eoe_fact_mono : forall a b : nat, (a <= b)%nat -> Qle (q_fact a) (q_fact b).
Proof.
  intros a b Hab.
  replace b with (a + (b - a))%nat by lia.
  apply eoe_fact_mono_add.
Qed.

(* §3 部分和序结构（支撑件 2：正项 ⟹ 递增；2/n! 恒正）             *)

Lemma eoe_q_pow_one : forall n : nat, q_pow 1 n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow 1 (Datatypes.S n)) with (1 * q_pow 1 n).
    rewrite IH. apply Qmult_1_l.
Qed.

Lemma eoe_two_fact_pos : forall n : nat, Qlt 0 ((1 + 1)%Q / q_fact n).
Proof.
  intro n.
  apply (eoe_lt_eq_l _ (0 * / q_fact n)).
  - rewrite Qmult_0_l. reflexivity.
  - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ q_fact n)).
    + apply Qinv_lt_0_compat. apply q_fact_pos.
    + unfold Qlt. simpl. lia.
Qed.

Lemma eoe_term_pos : forall n : nat,
  Qlt 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intro n.
  apply (eoe_lt_eq_r 0 (/ q_fact (Datatypes.S n))).
  - apply Qinv_lt_0_compat. apply q_fact_pos.
  - rewrite (eoe_q_pow_one (Datatypes.S n)).
    unfold Qdiv. symmetry. apply Qmult_1_l.
Qed.

Lemma eoe_step_pos : forall n : nat,
  Qlt 0 (exp_partial (Datatypes.S n) 1 - exp_partial n 1).
Proof.
  intro n.
  assert (Hd : exp_partial (Datatypes.S n) 1 - exp_partial n 1 ==
               q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
  { simpl. ring. }
  apply (eoe_lt_eq_r 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n))).
  - apply eoe_term_pos.
  - apply (Qeq_sym _ _). exact Hd.
Qed.

Lemma eoe_mono_add : forall d m : nat, Qle (exp_partial m 1) (exp_partial (m + d) 1).
Proof.
  intros d m. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    apply (Qle_trans _ (exp_partial (m + d) 1)).
    + exact IH.
    + apply (proj2 (Qle_minus_iff (exp_partial (m + d) 1)
                                  (exp_partial (Datatypes.S (m + d)) 1))).
      apply (Qlt_le_weak 0 (exp_partial (Datatypes.S (m + d)) 1 -
                            exp_partial (m + d) 1)).
      apply eoe_step_pos.
Qed.

Lemma eoe_mono : forall m n : nat, (m <= n)%nat -> Qle (exp_partial m 1) (exp_partial n 1).
Proof.
  intros m n Hmn.
  replace n with (m + (n - m))%nat by lia.
  apply eoe_mono_add.
Qed.

(* §4 尾界显式公式：m ≤ n ⟹ |S_n − S_m| ≤ 2/m!                    *)

Lemma eoe_one_abs : Qabs 1 == 1.
Proof. apply Qabs_pos. unfold Qle. simpl. lia. Qed.

Lemma eoe_q_pow_one_abs : forall n : nat, q_pow (Qabs 1) n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow (Qabs 1) (Datatypes.S n)) with (Qabs 1 * q_pow (Qabs 1) n).
    rewrite eoe_one_abs. rewrite IH. reflexivity.
Qed.

Lemma eoe_diff_bound : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1))
      ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q).
Proof.
  intros m n H1m Hmn.
  apply (exp_partial_diff_bound 1 (Qabs 1) m n).
  - reflexivity.
  - rewrite eoe_one_abs. unfold Qle. simpl. lia.
  - intros t Hmt. unfold Qle. simpl. lia.
  - exact Hmn.
Qed.

Lemma eoe_tail_explicit : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1)) ((1 + 1)%Q / q_fact m).
Proof.
  intros m n H1m Hmn.
  apply (Qle_trans _ ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q)).
  - apply (exp_partial_diff_bound 1 (Qabs 1) m n).
    + reflexivity.
    + rewrite eoe_one_abs. unfold Qle. simpl. lia.
    + intros t Hmt. unfold Qle. simpl. lia.
    + exact Hmn.
  - apply qeq_le.
    rewrite (eoe_q_pow_one_abs m). unfold Qdiv. ring.
Qed.

(* ---- 对称化（出口主用形）：1 ≤ n ≤ m ⟹ |S_m − S_n| ≤ 2/n! ---- *)
Lemma eoe_abs_Qle : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  Qle (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  apply (eoe_tail_explicit n m); assumption.
Qed.

Theorem eoe_abs_bound : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  apply Qle_to_QleT'.
  apply eoe_abs_Qle; assumption.
Qed.

(* §5 主件：e 的显式有理双区间（sigT 双端点 + 正隙宽 + 全后继夹逼） *)
(*   lo := S_n，hi := S_n + 2/n!，hi − lo == 2/n! > 0，           *)
(*   ∀ m ≥ n：lo ≤ S_m ≤ hi（即 S_n ≤ e 的任一后继近似 ≤ hi）。    *)

Theorem eoe_two_sided : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      prod (QltT' 0 (hi - lo))
           (forall m : nat, NatLe n m ->
              prod (QleT' lo (exp_partial m 1))
                   (QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) (hi - lo))))).
Proof.
  intros n H1n.
  exists (exp_partial n 1).
  exists (exp_partial n 1 + (1 + 1)%Q / q_fact n).
  split.
  - (* 隙宽显式：hi − lo == 2/n! > 0 *)
    apply Qlt_to_QltT'.
    assert (Hgap : (exp_partial n 1 + (1 + 1)%Q / q_fact n) - exp_partial n 1 ==
                   (1 + 1)%Q / q_fact n) by ring.
    rewrite Hgap. apply eoe_two_fact_pos.
  - intros m Hnm.
    assert (Hnm' : (n <= m)%nat) by (apply NatLe_drop in Hnm; exact Hnm).
    split.
    + (* 下翼：S_n ≤ S_m（正项递增） *)
      apply Qle_to_QleT'.
      apply eoe_mono. exact Hnm'.
    + (* 上翼：|S_m − S_n| ≤ hi − lo == 2/n!（隙宽显式） *)
      apply (qleT'_weaken _ ((1 + 1)%Q / q_fact n) _).
      * apply eoe_abs_Qle; assumption.
      * ring.
Qed.

(* §6 精度可计算支：N := S(ceil(2/eps)) 显式模量（B4 同款纪律）     *)

Definition eoe_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling ((1 + 1)%Q / eps))).

Lemma eoe_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt ((1 + 1)%Q / q_fact (eoe_modulus eps)) eps.
Proof.
  intros eps Hlt.
  unfold eoe_modulus.
  assert (Hinv0 : Qlt 0 (/ eps)) by (apply Qinv_lt_0_compat; exact Hlt).
  assert (H2e : Qlt 0 ((1 + 1)%Q / eps)).
  { apply (eoe_lt_eq_l _ (0 * / eps)).
    - rewrite Qmult_0_l. reflexivity.
    - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ eps)).
      + exact Hinv0.
      + unfold Qlt. simpl. lia. }
  remember (Qceiling ((1 + 1)%Q / eps)) as c eqn:Hcdef.
  assert (Hle : Qle ((1 + 1)%Q / eps) (c # 1)) by (rewrite Hcdef; apply Qle_ceiling).
  assert (Hc1 : (1 <= c)%Z).
  { assert (Hlt1 : Qlt 0 (c # 1))
      by (apply (Qlt_le_trans 0 ((1 + 1)%Q / eps) (c # 1)); assumption).
    unfold Qlt in Hlt1. simpl in Hlt1. lia. }
  assert (Hk : Z.of_nat (Z.to_nat c) = c) by lia.
  assert (Hceil : Qle ((1 + 1)%Q / eps) ((Z.of_nat (Z.to_nat c)) # 1))
    by (rewrite Hk; exact Hle).
  (* 2/eps ≤ k#1 ≤ k! ⟹ 2 ≤ k!·eps *)
  assert (H2fact : Qle ((1 + 1)%Q / eps) (q_fact (Z.to_nat c))).
  { apply (Qle_trans _ ((Z.of_nat (Z.to_nat c)) # 1)).
    - exact Hceil.
    - apply eoe_fact_ge_self. }
  assert (Hmul : Qle ((1 + 1)%Q / eps * eps) (q_fact (Z.to_nat c) * eps)).
  { apply Qmult_le_compat_r.
    - exact H2fact.
    - apply (Qlt_le_weak 0 eps). exact Hlt. }
  assert (Hid : (1 + 1)%Q / eps * eps == (1 + 1)%Q).
  { field. intro Hzz. apply (Qlt_not_eq 0 eps Hlt). exact (Qeq_sym _ _ Hzz). }
  assert (H2 : Qle (1 + 1)%Q (q_fact (Z.to_nat c) * eps)).
  { apply (Qle_trans _ ((1 + 1)%Q / eps * eps)).
    - apply qeq_le. symmetry. exact Hid.
    - exact Hmul. }
  (* N = S k 的阶乘 = (k+1)·k! ≥ 2·k!，严格衰减压过 eps *)
  assert (HN2 : Qle (1 + 1)%Q ((Z.of_nat (Datatypes.S (Z.to_nat c))) # 1)).
  { unfold Qle. simpl. lia. }
  assert (Hden : Qle ((1 + 1)%Q * q_fact (Z.to_nat c))
                     (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Z.to_nat c)) # 1) * q_fact (Z.to_nat c))).
    - apply Qmult_le_compat_r.
      + exact HN2.
      + apply (Qlt_le_weak 0 (q_fact (Z.to_nat c))). apply q_fact_pos.
    - apply qeq_le. reflexivity. }
  assert (Hstrict : Qlt (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
  { apply (eoe_lt_eq_l _ (1 * q_fact (Z.to_nat c))).
    - symmetry. apply Qmult_1_l.
    - apply (Qmult_lt_compat_r 1 (1 + 1)%Q (q_fact (Z.to_nat c))).
      + apply q_fact_pos.
      + unfold Qlt. simpl. lia. }
  assert (HqN : Qlt (q_fact (Z.to_nat c)) (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qlt_le_trans (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
    - exact Hstrict.
    - exact Hden. }
  assert (Hdrop : Qlt ((1 + 1)%Q / q_fact (Datatypes.S (Z.to_nat c)))
                      ((1 + 1)%Q / q_fact (Z.to_nat c))).
  { apply (eoe_div_lt (1 + 1)%Q (q_fact (Datatypes.S (Z.to_nat c))) (q_fact (Z.to_nat c))).
    - unfold Qlt. simpl. lia.
    - apply q_fact_pos.
    - apply q_fact_pos.
    - exact HqN. }
  assert (H2inv : Qle ((1 + 1)%Q * / q_fact (Z.to_nat c))
                      ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
  { apply Qmult_le_compat_r.
    - exact H2.
    - apply (Qlt_le_weak 0 (/ q_fact (Z.to_nat c))).
      apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hid2 : (q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c) == eps).
  { field. intro Hzz. apply (q_neq_of_lt (q_fact (Z.to_nat c)) (q_fact_pos (Z.to_nat c))).
    exact Hzz. }
  assert (Hfinal : Qle ((1 + 1)%Q / q_fact (Z.to_nat c)) eps).
  { apply (Qle_trans _ ((1 + 1)%Q * / q_fact (Z.to_nat c))).
    - apply qeq_le. reflexivity.
    - apply (Qle_trans _ ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
      + exact H2inv.
      + apply qeq_le. exact Hid2. }
  apply (Qlt_le_trans _ ((1 + 1)%Q / q_fact (Z.to_nat c))).
  - exact Hdrop.
  - exact Hfinal.
Qed.

(* ---- 出口二：sigT 柯西模量（N 显式 = ceil(2/eps)+1，可抽取） ---- *)
Theorem eoe_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (exp_partial m 1 - exp_partial n 1)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (eoe_modulus eps).
  intros m n HNm HNn.
  apply NatLe_drop in HNm.
  apply NatLe_drop in HNn.
  apply Qlt_to_QltT'.
  assert (HN1 : (1 <= eoe_modulus eps)%nat) by (unfold eoe_modulus; lia).
  assert (H1m : (1 <= m)%nat) by lia.
  assert (H1n : (1 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n：|S_n − S_m| ≤ 2/m! ≤ 2/N! < eps *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact m)).
      * rewrite Qabs_Qminus. apply (eoe_tail_explicit m n); assumption.
      * apply (eoe_div_le (1 + 1)%Q (q_fact m) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNm.
    + apply eoe_modulus_bound. exact Hlt.
  - (* n < m：|S_m − S_n| ≤ 2/n! ≤ 2/N! < eps *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact n)).
      * apply (eoe_tail_explicit n m); lia.
      * apply (eoe_div_le (1 + 1)%Q (q_fact n) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNn.
    + apply eoe_modulus_bound. exact Hlt.
Qed.

(* §7 假设留痕（红线④：Print Assumptions ≥ 1）                    *)

Print Assumptions eoe_two_sided.
Print Assumptions eoe_abs_bound.
Print Assumptions eoe_cauchy_modulus.
Print Assumptions eoe_mono.

Print Assumptions eoe_abs_bound.
Print Assumptions eoe_abs_Qle.
Print Assumptions qleT'_weaken.
Print Assumptions Qlt_to_QltT'.
Print Assumptions QltT'_to_Qlt.
(* ================= §6 m3_states 族 ================= *)
Import ListNotations.
From Stdlib Require Import QArith.Qring.
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== M3.0 基础定义 ========== *)

(* 离散状态表：n 个状态 [0;1;...;n-1]（list 离散状态世界） *)
Definition m3_states (n : nat) : list nat := seq 0 n.

(* KL 的 list 版：逐项 real_kl_term 折叠求和 *)
Definition m3_kl_list (n : nat) (f g : nat -> Real)
    (Hf : forall i : nat, real_lt real_zero (f i))
    (Hg : forall i : nat, real_lt real_zero (g i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (f i) (g i) (Hf i) (Hg i))
    (m3_states n).

(* 几何率底 κ := 1−η *)
Definition m3_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* κ 的 t 次幂（nat 重复乘）※ S 遮蔽 Datatypes.S，须限定名 *)
Fixpoint m3_rpow (a : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S t' => real_mult a (m3_rpow a t')
  end.

(* t·x（nat 重复加；逐步误差 eps 的 t 步累积） *)
Fixpoint m3_nmul (k : nat) (x : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S k' => real_plus x (m3_nmul k' x)
  end.

(* 1+1 > 0（对半预算的分母） *)
Lemma m3_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)           (real_plus real_one real_one)           (real_eq_sym (real_plus real_zero real_zero) real_zero              kl_zero_plus_zero)           (real_lt_plus_compat real_zero real_one real_zero real_one              real_lt_zero_one real_lt_zero_one)).
Qed.

(* eps 对半：d := eps·inv(1+1)（M3.1 的双 eps 预算合一） *)
Definition m3_half (eps : Real) : Real :=
  real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos).

Lemma m3_half_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (m3_half eps).
Proof.
  intros eps Heps.
  unfold m3_half.
  exact (real_mult_positive eps           (real_inv_pos (real_plus real_one real_one) m3_two_pos)           Heps           (real_inv_pos_pos (real_plus real_one real_one) m3_two_pos)).
Qed.

Lemma m3_half_double_eq : forall eps : Real,
  real_eq (real_plus (m3_half eps) (m3_half eps)) eps.
Proof.
  intros eps. unfold m3_half.
  set (dd := real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos)).
  set (two := real_plus real_one real_one).
  apply (real_eq_trans (real_plus dd dd) (real_mult two dd)).
  - exact (real_eq_trans (real_plus dd dd)
             (real_plus (real_mult real_one dd) (real_mult real_one dd))
             (real_mult two dd)
             (RealSetoid.real_eq_plus_compat dd dd
                (real_mult real_one dd) (real_mult real_one dd)
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd))
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd)))
             (kl_sum_prod_r real_one real_one dd)).
  - exact (real_eq_trans (real_mult two dd)
             (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
             eps
             (kl_swap3 two eps (real_inv_pos two m3_two_pos))
             (real_eq_trans
                (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
                (real_mult eps real_one)
                eps
                (RealSetoid.real_eq_mult_compat eps
                   (real_mult two (real_inv_pos two m3_two_pos)) eps real_one
                   (real_eq_refl eps)
                   (real_inv_pos_correct two m3_two_pos))
                (real_mult_one eps))).
Qed.

(* ========== 环 / 序辅助 ========== *)

(* η + (1−η) == 1 *)
Lemma m3_ring_eta_kappa : forall eta : Real,
  real_eq (real_plus eta (m3_kappa eta)) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. unfold m3_kappa.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* η < 1 ⟹ 0 < 1−η *)
Lemma m3_kappa_pos : forall eta : Real,
  real_lt eta real_one -> real_lt real_zero (m3_kappa eta).
Proof.
  intros eta Hlt.
  unfold m3_kappa.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < η ⟹ 1−η ≤ 1 *)
Lemma m3_kappa_le_one : forall eta : Real,
  real_lt real_zero eta -> real_le (m3_kappa eta) real_one.
Proof.
  intros eta Hpos. unfold m3_kappa. apply kl_lt_le_bridge.
  set (X := real_plus real_one (real_opp eta)).
  assert (Hstep1 : real_lt (real_plus real_zero X) (real_plus eta X))
    by exact (real_lt_plus_compat_lt_le real_zero eta X X Hpos (real_le_refl X)).
  assert (Hstep2 : real_lt (real_plus real_zero X) real_one)
    by exact (real_lt_eq_lt (real_plus real_zero X) (real_plus eta X) real_one
                Hstep1 (m3_ring_eta_kappa eta)).
  exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus real_zero X) real_one
           (real_eq_trans (real_plus real_one (real_opp eta)) X (real_plus real_zero X)
              (real_eq_refl X)
              (real_eq_sym (real_plus real_zero X) X (kl_plus_zero_l X)))
           Hstep2).
Qed.

(* κ ≤ 1、0 ≤ y ⟹ κ·y ≤ y *)
Lemma m3_le_kappa_mul : forall kappa y : Real,
  real_le real_zero y -> real_le kappa real_one ->
  real_le (real_mult kappa y) y.
Proof.
  intros kappa y Hy0 Hk1.
  apply (kl_le_eq_r (real_mult kappa y) (real_mult real_one y) y).
  - exact (real_le_mult_compat_weak kappa real_one y Hy0 Hk1).
  - apply kl_mult_one_l.
Qed.

(* 0 ≤ c、a ≤ b ⟹ c·a ≤ c·b（左乘版） *)
Lemma m3_le_mult_compat_l : forall c a b : Real,
  real_le real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc Hab.
  apply (kl_le_eq_r (real_mult c a) (real_mult b c) (real_mult c b)).
  - apply (kl_le_eq_l (real_mult a c) (real_mult b c) (real_mult c a)).
    + exact (real_le_mult_compat_weak a b c Hc Hab).
    + apply real_mult_comm.
  - apply real_mult_comm.
Qed.

(* 环：a·(b+c) == a·b + a·c *)
Lemma m3_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环：a·(b·c) == (a·b)·c *)
Lemma m3_ring_reassoc2 : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < x ⟹ 0 ≤ t·x *)
Lemma m3_nmul_nonneg : forall (k : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (m3_nmul k x).
Proof.
  intros k x Hx. induction k as [| k IH].
  - apply real_le_refl.
  - exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus x (m3_nmul k x)) real_zero
             (real_le_plus_compat real_zero x real_zero (m3_nmul k x)
                (kl_lt_le_bridge real_zero x Hx) IH)
             kl_zero_plus_zero).
Qed.

(* n ≠ 0 ⟹ 状态表非空 *)
Lemma m3_seq_nonnil : forall n : nat, n <> 0 -> m3_states n <> nil.
Proof.
  intros n Hn Hnil. unfold m3_states in Hnil.
  destruct n as [| m].
  - exact (Hn eq_refl).
  - simpl in Hnil. discriminate Hnil.
Qed.

(* 逐项正项的 list 和为正（配分函数正性核） *)
Lemma m3_interp_Z_pos2 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k e : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero
    (real_list_sum nat
       (fun i : nat => real_mult
          (real_pow_pos (q i) k (Hq i)) (real_pow_pos (r i) e (Hr i)))
       (m3_states n)).
Proof.
  intros n Hn q r k e Hq Hr.
  apply (real_list_sum_pos nat).
  - intro i.
    exact (real_mult_positive (real_pow_pos (q i) k (Hq i))
             (real_pow_pos (r i) e (Hr i))
             (cauchy_real_exp_pos (real_mult k (cw_log (q i) (Hq i))))
             (cauchy_real_exp_pos (real_mult e (cw_log (r i) (Hr i))))).
  - exact (m3_seq_nonnil n Hn).
Qed.

(* 同上，结论取 real_interp_Z 原生形态（供 pkg 的 sigT 组件直接对型） *)
Lemma m3_interp_Z_pos3 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n q r k Hq Hr).
Proof.
  intros n Hn q r k Hq Hr.
  exact (m3_interp_Z_pos2 n Hn q r (real_plus real_one (real_opp k)) k Hq Hr).
Qed.

(* 单步更新逐点正性：π'(i) := (r(i)^{1−k}·p(i)^k)·inv Z > 0 *)
Definition m3_step_pos_pt (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp))
    (i : nat)
  : real_lt real_zero (real_step_next n r p k Hr Hp HZ i) :=
  real_mult_positive
    (real_mult (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
               (real_pow_pos (p i) k (Hp i)))
    (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
    (real_mult_positive
       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
       (real_pow_pos (p i) k (Hp i))
       (cauchy_real_exp_pos
          (real_mult (real_plus real_one (real_opp k)) (cw_log (r i) (Hr i))))
       (cauchy_real_exp_pos (real_mult k (cw_log (p i) (Hp i)))))
    (real_inv_pos_pos (real_interp_Z n r p k Hr Hp) HZ).

(* 单步更新归一化：Σ π' == inv Z·Z == 1（配分函数吸收） *)
Lemma m3_step_next_norm : forall (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp)),
  real_eq
    (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
    real_one.
Proof.
  intros n r p k Hr Hp HZ.
  exact (real_eq_trans           (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))           (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                      (real_list_sum nat                         (fun i : nat => real_mult                            (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                            (real_pow_pos (p i) k (Hp i)))                         (m3_states n)))           real_one           (real_list_sum_linear_r nat              (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)              (fun i : nat => real_mult                 (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                 (real_pow_pos (p i) k (Hp i)))              (m3_states n))           (real_eq_trans              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_list_sum nat                            (fun i : nat => real_mult                               (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                               (real_pow_pos (p i) k (Hp i)))                            (m3_states n)))              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_interp_Z n r p k Hr Hp))              real_one              (RealSetoid.real_eq_mult_compat                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_list_sum nat                    (fun i : nat => real_mult                       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                       (real_pow_pos (p i) k (Hp i)))                    (m3_states n))                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_interp_Z n r p k Hr Hp)                 (real_eq_refl (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 (real_eq_refl (real_interp_Z n r p k Hr Hp)))              (real_eq_trans                 (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                            (real_interp_Z n r p k Hr Hp))                 (real_mult (real_interp_Z n r p k Hr Hp)                            (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 real_one                 (real_mult_comm (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                                 (real_interp_Z n r p k Hr Hp))                 (real_inv_pos_correct (real_interp_Z n r p k Hr Hp) HZ)))).
Qed.

(* ========== 策略迭代序列（sigT 封装：策略+正性+配分函数正性+归一化） ========== *)

(* 迭代包类型：p := π_t 连同其逐点正性、下一步配分函数正性、归一化恒等 *)
Definition m3_pkg_type (n : nat) (r : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) : Type :=
  { p : nat -> Real &
    { Hp : forall i : nat, real_lt real_zero (p i) &
      { HZ : real_lt real_zero (real_interp_Z n r p (m3_kappa eta) Hr Hp) &
        real_eq (real_list_sum nat p (m3_states n)) real_one } } }.

(* π_{t+1}(i) := real_step_next n r π_t (1−η)：几何插值策略更新
   π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z_t。
   单 Fixpoint（对 t 结构递归），O 情形携带初值四元组，
   S 情形经 m3_step_pos_pt / m3_interp_Z_pos2 / m3_step_next_norm
   同步重建四元组。 *)
Fixpoint m3_pi_pkg (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) {struct t} : m3_pkg_type n r eta Hr :=
  match t with
  | Datatypes.O => existT _ p0 (existT _ Hp0 (existT _ HZ1 Hnorm0))
  | Datatypes.S t' =>
      let pkg := m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t' in
      let p := projT1 pkg in
      let Hp := projT1 (projT2 pkg) in
      let HZ := projT1 (projT2 (projT2 pkg)) in
      (existT _ (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
         (existT _ (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)
           (existT
              (fun HZ' : real_lt real_zero
                          (real_interp_Z n r
                             (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                             (m3_kappa eta) Hr
                             (fun i : nat =>
                                m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)) =>
                 real_eq
                   (real_list_sum nat
                      (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                      (m3_states n))
                   real_one)
              (m3_interp_Z_pos3 n Hn r
                 (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                 (m3_kappa eta) Hr
                 (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i))
              (m3_step_next_norm n r p (m3_kappa eta) Hr Hp HZ)))
       : m3_pkg_type n r eta Hr)
  end.

(* 四投影：迭代策略序列 / 逐点正性 / 配分函数正性 / 归一化 *)
Definition m3_pi_seq (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) : nat -> Real :=
  projT1 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t).

Definition m3_pi_seq_pos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  forall i : nat,
    real_lt real_zero (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t i) :=
  fun i : nat => projT1 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) i.

Definition m3_pi_seq_Zpos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_lt real_zero
    (real_interp_Z n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
       (m3_kappa eta) Hr (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) :=
  projT1 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

Definition m3_pi_seq_norm (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_eq
    (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) (m3_states n))
    real_one :=
  projT2 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

(* ========== M3.1 前置：M2 换向单步几何收缩（eps 化 geom_step） ========== *)

(* 单步真几何率（根内 policy_iter_kl_geom_step 的 eps 化副本）：
   KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + eps。
   即 UpStepKL 的 M2（real_step_kl_eta_bound_eps）在迭代序列第 t 步的
   直接实例化：p-槽 := r（π*），r-槽 := π_t，eta-槽 := κ := 1−η。 *)
Corollary real_iter_step_geom_eps :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       eps).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  exact (real_step_kl_eta_bound_eps n r           (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_kappa eta) Hr           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           Hnormr (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))           (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)           eps Heps).
Qed.

(* ========== M3.1：单步向后 KL 递推（backward_kl_step_le 的 eps 化副本） ========== *)
(* KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1}) + eps
   路线（对应根内 policy_iter_backward_kl_step_le 的「丢弃负项」）：
   M2 换向实例给 KL(π*‖π_{t+1}) ≤ (1−η)KL(π*‖π_t) + d（d := eps/2），
   Gibbs 下界给 0 ≤ KL(π_t‖π_{t+1}) + d，两式相加后对半预算吸收 eps。 *)
Theorem real_iter_kl_step :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       (real_plus
          (m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
          eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  assert (HnormP : forall s : nat,
            real_eq
              (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 s)
                 (m3_states n))
              real_one)
    by exact (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0).
  set (A := real_mult (m3_kappa eta)
              (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                 (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).
  set (B := m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))).
  set (d := m3_half eps).
  apply (real_le_trans
           (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
           (real_plus (real_plus A d) (real_plus B d))
           (real_plus A (real_plus B eps))).
  - apply (real_le_trans
             (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
                (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
             (real_plus A d)
             (real_plus (real_plus A d) (real_plus B d))).
    + (* M2 换向实例：KL(π*‖π_{t+1}) ≤ κ·KL(π*‖π_t) + d *)
      exact (real_step_kl_eta_bound_eps n r
               (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_kappa eta) Hr
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               Hnormr (HnormP t)
               (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
               (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
               d (m3_half_pos eps Heps)).
    + (* (A+d) ≤ (A+d) + (B+d)：Gibbs 下界 0 ≤ B + d *)
      exact (kl_le_eq_l (real_plus (real_plus A d) real_zero)
               (real_plus (real_plus A d) (real_plus B d))
               (real_plus A d)
               (real_le_plus_compat (real_plus A d) (real_plus A d)
                  real_zero (real_plus B d)
                  (real_le_refl (real_plus A d))
                  (real_gibbs_inequality_eps nat (m3_states n)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (HnormP t) (HnormP (Datatypes.S t)) d (m3_half_pos eps Heps)))
               (real_plus_zero (real_plus A d))).
  - (* eq 换形：(A+d)+(B+d) == A+(B+eps) *)
    exact (kl_eq_le_bridge (real_plus (real_plus A d) (real_plus B d))
             (real_plus A (real_plus B eps))
             (real_eq_trans (real_plus (real_plus A d) (real_plus B d))
             (real_plus (real_plus A B) (real_plus d d))
             (real_plus A (real_plus B eps))
             (real_plus_swap_mid A d B d)
             (real_eq_trans (real_plus (real_plus A B) (real_plus d d))
                (real_plus (real_plus A B) eps)
                (real_plus A (real_plus B eps))
                (RealSetoid.real_eq_plus_compat (real_plus A B) (real_plus d d)
                   (real_plus A B) eps
                   (real_eq_refl (real_plus A B))
                   (m3_half_double_eq eps))
                (real_eq_sym (real_plus A (real_plus B eps))
                   (real_plus (real_plus A B) eps)
                   (real_plus_assoc A B eps))))).
Qed.

(* ========== M3.2：真几何率迭代（geom_iter 的 eps 化副本） ========== *)
(* KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps
   （根内 policy_iter_kl_geom_iter 的 eps 化副本：单步收缩
     real_iter_step_geom_eps 对 t 归纳，误差按 t 步算术累积。） *)
Theorem real_iter_kl_geom :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))
    (real_plus
       (real_mult (m3_rpow (m3_kappa eta) t)
          (m3_kl_list n r p0 Hr Hp0))
       (m3_nmul t eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1
         t eps Heps.
  induction t as [| t IH].
  - (* t = 0：κ^0 == 1、0·eps == 0，KL ≤ 1·KL + 0 == KL *)
    cbn [m3_rpow m3_nmul].
    apply kl_eq_le_bridge.
    apply (real_eq_sym
             (real_plus
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero)
             (m3_kl_list n r p0 Hr Hp0)).
    exact (real_eq_trans
             (real_plus (real_mult real_one (m3_kl_list n r p0 Hr Hp0))
                        real_zero)
             (real_plus (m3_kl_list n r p0 Hr Hp0) real_zero)
             (m3_kl_list n r p0 Hr Hp0)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero
                (m3_kl_list n r p0 Hr Hp0) real_zero
                (kl_mult_one_l (m3_kl_list n r p0 Hr Hp0))
                (real_eq_refl real_zero))
             (real_plus_zero (m3_kl_list n r p0 Hr Hp0))).
  - (* t = S t：单步收缩 + IH 单调放大 + κ 系数重排 + 误差累积 *)
    cbn [m3_rpow m3_nmul].
    pose proof (real_iter_step_geom_eps n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                  Hnormr Heta_pos Heta_lt1 t eps Heps) as Hstep.
    set (KL0 := m3_kl_list n r p0 Hr Hp0).
    set (KLt := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)).
    set (KLs := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                  Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                     (Datatypes.S t))).
    set (Y := m3_nmul t eps).
    set (X := real_mult (m3_rpow (m3_kappa eta) t) KL0).
    (* κ·单调：0 ≤ κ、IH ⟹ κ·KL_t ≤ κ·(κ^t·KL0 + t·eps) *)
    assert (Hmono : real_le (real_mult (m3_kappa eta) KLt)
                            (real_mult (m3_kappa eta) (real_plus X Y))).
    { apply (m3_le_mult_compat_l (m3_kappa eta)).
      - exact (kl_lt_le_bridge real_zero (m3_kappa eta)
                 (m3_kappa_pos eta Heta_lt1)).
      - exact IH. }
    (* 单步链：KL_{t+1} ≤ κ·KL_t + eps ≤ κ·(κ^t·KL0 + Y) + eps *)
    assert (Hchain : real_le KLs
                       (real_plus (real_mult (m3_kappa eta) (real_plus X Y))
                          eps)).
    { apply (real_le_trans KLs (real_plus (real_mult (m3_kappa eta) KLt) eps)).
      - exact Hstep.
      - exact (real_le_plus_compat (real_mult (m3_kappa eta) KLt)
                  (real_mult (m3_kappa eta) (real_plus X Y)) eps eps
                  Hmono (real_le_refl eps)). }
    (* 终组装：κ·(X+Y)+eps ≤ (κ·κ^t)·KL0 + (Y+eps)（κ·Y ≤ Y） *)
    apply (real_le_trans KLs
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps))
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus eps Y))).
    + apply (kl_le_eq_r _ (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)).
      * exact Hchain.
      * exact (real_eq_trans
                 (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)
                 (real_plus (real_plus (real_mult (m3_kappa eta) X)
                              (real_mult (m3_kappa eta) Y)) eps)
                 (real_plus
                    (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                       KL0)
                    (real_plus (real_mult (m3_kappa eta) Y) eps))
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (m3_kappa eta) (real_plus X Y))
                    eps
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_mult (m3_kappa eta) Y))
                    eps
                    (m3_distrib_l (m3_kappa eta) X Y)
                    (real_eq_refl eps))
                 (real_eq_trans
                    (real_plus
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y)) eps)
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_plus
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_eq_sym
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_plus (real_mult (m3_kappa eta) Y) eps))
                       (real_plus
                          (real_plus (real_mult (m3_kappa eta) X)
                             (real_mult (m3_kappa eta) Y)) eps)
                       (real_plus_assoc (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y) eps))
                    (RealSetoid.real_eq_plus_compat
                       (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (m3_ring_reassoc2 (m3_kappa eta) (m3_rpow (m3_kappa eta) t) KL0)
                       (real_eq_refl (real_plus (real_mult (m3_kappa eta) Y) eps))))).
    + exact (real_le_plus_compat
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps)
                (real_plus eps Y)
                (real_le_refl
                   (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0))
                (kl_le_eq_r
                   (real_plus (real_mult (m3_kappa eta) Y) eps)
                   (real_plus Y eps)
                   (real_plus eps Y)
                   (real_le_plus_compat (real_mult (m3_kappa eta) Y) Y eps eps
                      (m3_le_kappa_mul (m3_kappa eta) Y
                         (m3_nmul_nonneg t eps Heps)
                         (m3_kappa_le_one eta Heta_pos))
                      (real_le_refl eps))
                   (real_plus_comm Y eps))).
Qed.

Print Assumptions real_iter_step_geom_eps.
Print Assumptions m3_step_next_norm.
Print Assumptions m3_interp_Z_pos3.
Print Assumptions m3_kappa_pos.
Print Assumptions m3_half_pos.
Print Assumptions m3_two_pos.
