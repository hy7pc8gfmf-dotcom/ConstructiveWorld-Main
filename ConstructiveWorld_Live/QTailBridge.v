(* ============================================================ *)
(* ToyR 玩具证替换件 —— T266 台账席 战役包AA（tier2 十七批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   qtb_qtail_sum_eq_exp_tail_T（原 L111，3 句玩具证）                   *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T330 恒等守恒更正注记】2026-09-22 包AW十 台账席（恒等头注更正全量第三批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T330 台账。                   *)
(* 附记：T277 判级全文恒等；包AA A-L 包域（AA/AB/AC/AD）第三批整批直推（T317 六·1 方案①）         *)
(* ============================================================ *)

(* ============================================================ *)
(* QTailBridge.v —— 席CWA：S03 exp_tail 与 UpReqQExpTail qtail_sum   *)
(*                  桥式恒等式闭合（E-STAGING-CWA 任务 1）            *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 使命（台账原文）：UpReqQExpTail.v:8 与 :755-756 遗留注记            *)
(*   「qtail_sum b m n == exp_tail (pred m) (pred n) b（m,n ≥ 1，    *)
(*   恒等式未证，仅注记）」——本件以归纳法真证闭合。                   *)
(*                                                                 *)
(* 数学内容：                                                       *)
(*   qtail_sum b m n = Σ_{k=m}^{n-1} b^k/k!（正指标，Fixpoint 于 n，  *)
(*     每步落 b^{n'}/n'!，n<m 守卫空和 = 0）；                       *)
(*   exp_tail m n x = Σ_{k=m}^{n-1} x^{S k}/(S k)!（指标错位 1）。    *)
(*   换指标 j = S k 即得 exp_tail (pred m) (pred n) b                *)
(*     = Σ_{j=m}^{n-1} b^j/j! = qtail_sum b m n（m,n ≥ 1）。          *)
(*   归纳核（qtb_bridge_aux）：对 n 归纳证                            *)
(*     qtail_sum b m (S n) == exp_tail (pred m) n b（1 ≤ m）。        *)
(*   边界两处 pred 处理：                                            *)
(*   ① 基座 n=0：m ≥ 1 时 qtail_sum b m 1 空（m ≤? 0 为 false），      *)
(*      exp_tail _ 0 _ 定义性 0；m=0 时恒等式确实失效（b^0/0! = 1      *)
(*      ≠ 0）——故 1 ≤ m 是必要前提非技术性装饰。                      *)
(*   ② 步进：守卫换算 (m ≤? S n'') ↔ (pred m ≤? n'') 无条件成立，       *)
(*      项指标 S n'' 两侧同形；不一致支经 qtb_pred_sub（pred m =      *)
(*      m-1）喂 lia 消去（E236 卡：pred 不直接代入 lia，先归约到 nat 减法）。*)
(*                                                                 *)
(* 红线自审：                                                       *)
(*   —— 禁词全零（scan_redline.py 全文件计）；无 公理/承认件/       *)
(*      参数/猜想/弃证，全 Qed 真证，零降级占位；          *)
(*   —— 结论面 Set 层：主定理 qtb_qtail_sum_eq_exp_tail_T 出口        *)
(*      QeqT（S02 Set 层 Q 相等），Qeq 形伴件仅供桥接（证明内核       *)
(*      惯例在 Qeq 内推理，同 UpReqQExpTail 头注口径）；语句面无       *)
(*      Qlt/Qle/exists/and/or Prop 命题出场，无 -> False；前提位       *)
(*      (1 <= m)%nat 为 nat 层指标前提（库内通例，非 Prop 泄露）。     *)
(*   —— 非平凡：归纳 + 双 guard 分支消去 + pred 双边界，非平凡交付。   *)
(*   —— G3 提取检验 Obj.magic=0（Recursive Extraction 两主定理）。    *)
(*                                                                 *)
(* 编译配方（cpu_guard 温控包装，基座 S01/S02/S03/UpReqQExpTail       *)
(* .vo 已在 Live/build）：                                           *)
(*   bash Live/tools/cpu_guard.sh -c \                               *)
(*     "cd Live/build && rocq c -Q . \"\" QTailBridge.v"             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqQExpTail.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== 件 0：pred → nat 减法桥（供 lia；E236 卡 pred 直接代入不稳） ===== *)

Lemma qtb_pred_sub : forall m : nat, Nat.pred m = (m - 1)%nat.
Proof.
  intros m. rewrite Nat.sub_1_r. reflexivity.
Qed.

(* ===== 件 1：归纳核（m ≥ 1 固定，对尾指标 n 归纳） =====
   qtail_sum b m (S n) == exp_tail (pred m) n b。
   基座 n=0 用 m ≥ 1 消守卫；步进做双 guard 换算 + 项指标对齐。 *)

Lemma qtb_bridge_aux : forall (b : Q) (n m : nat),
  (1 <= m)%nat -> qtail_sum b m (Datatypes.S n) == exp_tail (Nat.pred m) n b.
Proof.
  intros b n. induction n as [| n IH]; intros m Hm.
  - (* 基座 n = 0：qtail_sum b m 1 空（m ≥ 1）== exp_tail (pred m) 0 = 0 *)
    change (qtail_sum b m (Datatypes.S 0))
      with ((if Nat.leb m 0 then q_pow b 0 / q_fact 0 else 0)
            + qtail_sum b m 0).
    destruct (Nat.leb m 0) eqn:E.
    + apply Nat.leb_le in E. exfalso. lia.
    + reflexivity.
  - (* 步进 n → S n：两侧 change 展开 Fixpoint 一步（勿 simpl，E236 卡） *)
    change (qtail_sum b m (Datatypes.S (Datatypes.S n)))
      with ((if Nat.leb m (Datatypes.S n)
             then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
             else 0)
            + qtail_sum b m (Datatypes.S n)).
    change (exp_tail (Nat.pred m) (Datatypes.S n) b)
      with (exp_tail (Nat.pred m) n b
            + (if Nat.leb (Nat.pred m) n
               then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
               else 0)).
    rewrite (IH m Hm).
    destruct (Nat.leb m (Datatypes.S n)) eqn:E1;
      destruct (Nat.leb (Nat.pred m) n) eqn:E2.
    + (* 双真：同项同和，加法交换 *) ring.
    + (* 左真右假矛盾：n < pred m 且 m ≤ S n *)
      apply Nat.leb_le in E1.
      apply Nat.leb_gt in E2. rewrite qtb_pred_sub in E2. exfalso. lia.
    + (* 左假右真矛盾：S n < m 且 pred m ≤ n *)
      apply Nat.leb_gt in E1.
      apply Nat.leb_le in E2. rewrite qtb_pred_sub in E2. exfalso. lia.
    + (* 双假：双空和 *) ring.
Qed.

(* ===== 件 2：主定理（Qeq 层，台账原文语句形） ===== *)

Theorem qtb_qtail_sum_eq_exp_tail : forall (b : Q) (m n : nat),
  (1 <= m)%nat -> (1 <= n)%nat ->
  qtail_sum b m n == exp_tail (Nat.pred m) (Nat.pred n) b.
Proof.
  intros b m n Hm Hn.
  destruct n as [| n'].
  - exfalso. lia.
  - change (Nat.pred (Datatypes.S n')) with n'.
    apply (qtb_bridge_aux b n' m Hm).
Qed.

(* ===== 件 3：Set 层出口（QeqT，红线 2 语句面） ===== *)

Theorem qtb_qtail_sum_eq_exp_tail_T : forall (b : Q) (m n : nat),
  (1 <= m)%nat -> (1 <= n)%nat ->
  QeqT (qtail_sum b m n) (exp_tail (Nat.pred m) (Nat.pred n) b).
Proof.
  intros b m n Hm Hn.
  apply qeq_imp_qeqT.
  apply qtb_qtail_sum_eq_exp_tail; assumption.
Qed.

(* ===== 件 4：可计算性端到端核验（vm_compute 实例，G3 友好叶子） ===== *)
(* qtail_sum 3 1 5 = Σ_{k=1}^{4} 3^k/k! = 3 + 9/2 + 9/2 + 27/8 = 123/8
   exp_tail 0 4 3  = Σ_{k=0}^{3} 3^{k+1}/(k+1)! = 同上 —— 换指标逐项同形 *)

Lemma qtb_eval_example : QeqT (qtail_sum (3 # 1) 1%nat 5%nat)
                              (exp_tail 0%nat 4%nat (3 # 1)).
Proof. vm_compute. reflexivity. Qed.

(* ===== G4：主定理假设全 Closed（证据在编译日志） ===== *)

Print Assumptions qtb_qtail_sum_eq_exp_tail.
Print Assumptions qtb_qtail_sum_eq_exp_tail_T.
