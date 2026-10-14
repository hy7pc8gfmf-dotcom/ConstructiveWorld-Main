(* ===================================================================== *)
(*  zzm1_gauss.v —— Q(i) 残数算术组机·层 1 Z[i] 基座（DM-ZZM1·切片 1·ZZM-1）    *)
(*  模块名：zzm1_gauss。池：abl_dmw1_pool/ZZ/（ZZ 池对照域 _mirror_zz.py      *)
(*         MIRROR_GREEN 10/10 在卷·设计单 _tdmZZ2_Qi组机勘形 §三·三   *)
(*         需新铸五件之第 1 件）。                                            *)
(*  使命：高斯整数基座 gz（Z×Z 对偶承载·Record·律二字段位 Set）＋六运算        *)
(*        （add/neg/sub/mul/conj/eqb）＋gz_pow＋除法自由形 gz_im_neg_frac      *)
(*        （分子 −Im[e^j]·分母 norm^j 分离走 Z·读出位 Qmake——对照件             *)
(*        im_neg_power 直译·禁高斯除法）＋基座引理 10 条（norm 乘性·conj       *)
(*        乘性·Im[z̄]=−Im z·Im[(z̄)^j]=−Im[z^j]＝对照域红笔位 Coq 形依据）。       *)
(*  构造性注记：零 Axiom／零 Admitted／零 solver；一切语句 Set 承载（zzId        *)
(*        单态等词·Prop 等词仅存在于证明体内构造性推导）；定义一律 Defined。   *)
(*  忠实披露：gnorm 取 |z|² 档（norm 乘性＝|zw|²=|z|²|w|²·对照红笔③           *)
(*        |4+2i|²=20 档即此）；「残数=围道端点取值差」的复分析面（Cauchy       *)
(*        基座·库无）走诚实接口披露＝设计单层 2 披露位，非本件义务。           *)
(*  依赖：仅 Stdlib QArith/ZArith/List（设计单 ZZM-1 行·零世界播种）。         *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&          *)
(*        ulimit -s 65532 && cd 本池 && bash cpu_guard.sh -- rocq c            *)
(*        -native-compiler no -q -Q _world "" zzm1_gauss.v                     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ============================================================ *)
(* §0 Set 层单态等词（S01_BaseRing Id 同形·池内前缀命名 zzId——   *)
(*    入库时照邻件同名五步映射）                                  *)
(* ============================================================ *)

Inductive zzId {A : Set} (x : A) : A -> Set :=
| zzIdR : zzId x x.

Arguments zzIdR {A} {x}.

(* 布尔等词提取/回注（证明体内构造性 Prop 推导合法·信息无损） *)
Definition zzId_true {b : bool} (p : zzId b true) : b = true :=
  match p in zzId _ y return b = y with
  | zzIdR => eq_refl
  end.

(* 回注：布尔等式的 Set 层等词承载（eq_rect 逆向运输·构造性） *)
Definition zzId_bool {b : bool} (H : b = true) : zzId b true :=
  eq_rect true (fun y => zzId y true) zzIdR b (eq_sym H).

(* 通用反射件：Set 层等词从 Prop 等词回注（eq_rect 正向运输） *)
Definition zzId_from_eq {A : Set} {x y : A} (H : x = y) : zzId x y :=
  eq_rect x (fun z => zzId x z) zzIdR y H.

(* Q 布尔等词反射件：Qeq_bool x x = true 的 Set 承载（符号项可用的自反；
   stdlib Qeq_bool = Qnum 交叉积 Z.eqb 形·无 andb 分量） *)
Lemma zzId_Qeqb_refl : forall x : Q, zzId (Qeq_bool x x) true.
Proof.
  intros [a n]. unfold Qeq_bool; simpl.
  apply zzId_from_eq. apply Z.eqb_eq. ring.
Qed.

(* ============================================================ *)
(* §1 高斯整数基座（Z×Z 对偶承载）＋六运算＋幂＋除法自由形                        *)
(* ============================================================ *)

Record gz : Set := mkz { gre : Z ; gim : Z }.

Definition gz_zero : gz := mkz 0 0.
Definition gz_one : gz := mkz 1 0.

Definition gz_add (z w : gz) : gz := mkz (gre z + gre w) (gim z + gim w).
Definition gz_neg (z : gz) : gz := mkz (- gre z) (- gim z).
Definition gz_sub (z w : gz) : gz := gz_add z (gz_neg w).
Definition gz_mul (z w : gz) : gz :=
  mkz (gre z * gre w - gim z * gim w) (gre z * gim w + gim z * gre w).
Definition gnorm (z : gz) : Z := gre z * gre z + gim z * gim z.
Definition gz_conj (z : gz) : gz := mkz (gre z) (- gim z).
Definition gz_eqb (z w : gz) : bool :=
  andb (Z.eqb (gre z) (gre w)) (Z.eqb (gim z) (gim w)).

Fixpoint gz_pow (z : gz) (j : nat) : gz :=
  match j with
  | O => gz_one
  | S k => gz_mul (gz_pow z k) z
  end.

(* 除法自由形（设计单第 2 件·对照件 im_neg_power 直译）：
   Im[(a+bi)^{−j}] = −Im[(a+bi)^j] / (a²+b²)^j —— 分子分母分离走 Z，
   读出位 Qmake·禁高斯除法·gcd 免除。 *)
Definition gz_im_neg_frac (e : gz) (j : nat) : Z * Z :=
  (Z.opp (gim (gz_pow e j)), gnorm (gz_pow e j)).

(* Z 幂（nat 档·norm 幂读出用） *)
Fixpoint zpow (a : Z) (j : nat) : Z :=
  match j with
  | O => 1
  | S k => a * zpow a k
  end.

(* ============================================================ *)
(* §2 基座引理 10 条（全部 Set 承载·零 solver）                                  *)
(* ============================================================ *)

Lemma gz_add_comm_b : forall z w : gz, zzId (gz_eqb (gz_add z w) (gz_add w z)) true.
Proof.
  intros [a b] [c d]. unfold gz_add, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

Lemma gz_add_assoc_b : forall z w u : gz,
  zzId (gz_eqb (gz_add (gz_add z w) u) (gz_add z (gz_add w u))) true.
Proof.
  intros [a b] [c d] [e f]. unfold gz_add, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

Lemma gz_mul_comm_b : forall z w : gz, zzId (gz_eqb (gz_mul z w) (gz_mul w z)) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

(* norm 乘性：|zw|² = |z|²|w|²（lagrange 恒等式·ring 判定） *)
Lemma gnorm_mul_b : forall z w : gz,
  zzId (Z.eqb (gnorm (gz_mul z w)) (gnorm z * gnorm w)) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gnorm; simpl.
  apply zzId_from_eq. apply Z.eqb_eq; ring.
Qed.

(* conj 乘性 *)
Lemma gz_conj_mul_b : forall z w : gz,
  zzId (gz_eqb (gz_conj (gz_mul z w)) (gz_mul (gz_conj z) (gz_conj w))) true.
Proof.
  intros [a b] [c d]. unfold gz_mul, gz_conj, gz_eqb; simpl.
  apply zzId_from_eq. apply andb_true_intro; split; apply Z.eqb_eq; ring.
Qed.

(* Im[z̄] = −Im z *)
Lemma gz_im_conj_b : forall z : gz,
  zzId (Z.eqb (gim (gz_conj z)) (Z.opp (gim z))) true.
Proof.
  intros [a b]. unfold gz_conj; simpl.
  apply zzId_from_eq. apply Z.eqb_eq; ring.
Qed.

(* gz_eqb 自反（Z.eqb_refl 直用·符号项可用） *)
Lemma gz_eqb_refl : forall z : gz, gz_eqb z z = true.
Proof.
  intros z. unfold gz_eqb. apply andb_true_intro; split; apply Z.eqb_refl.
Qed.

(* 幂步进（定义性） *)
Lemma gz_pow_succ_b : forall (z : gz) (j : nat),
  zzId (gz_eqb (gz_pow z (S j)) (gz_mul (gz_pow z j) z)) true.
Proof.
  intros z j. apply zzId_from_eq.
  change (gz_eqb (gz_mul (gz_pow z j) z) (gz_mul (gz_pow z j) z) = true).
  apply gz_eqb_refl.
Qed.

(* norm 幂性：|z^j|² = (|z|²)^j *)
Lemma gnorm_pow_b : forall (z : gz) (j : nat),
  zzId (Z.eqb (gnorm (gz_pow z j)) (zpow (gnorm z) j)) true.
Proof.
  intros z j; induction j as [|j IH]; cbn [gz_pow zpow].
  - apply zzId_from_eq. reflexivity.
  - pose proof (gnorm_mul_b (gz_pow z j) z) as Hm.
    apply zzId_true in Hm. apply Z.eqb_eq in Hm. rewrite Hm.
    pose proof (IH) as Hi. apply zzId_true in Hi. apply Z.eqb_eq in Hi. rewrite Hi.
    apply zzId_from_eq. apply Z.eqb_eq. ring.
Qed.

(* gz_eqb 完备（证明体构造性 Prop 推导·辅助件） *)
Lemma gz_eqb_true : forall z w : gz, gz_eqb z w = true -> z = w.
Proof.
  intros [a b] [c d] H. unfold gz_eqb in H; simpl in H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

(* 共轭幂：Im[(z̄)^j] = −Im[z^j]（对照件 im_neg_power 的 Coq 形依据·全件形式） *)
Lemma gz_pow_conj_b : forall (z : gz) (j : nat),
  zzId (gz_eqb (gz_pow (gz_conj z) j) (gz_conj (gz_pow z j))) true.
Proof.
  intros z j; induction j as [|j IH]; cbn [gz_pow].
  - apply zzId_from_eq. reflexivity.
  - pose proof (gz_conj_mul_b (gz_pow z j) z) as Hc.
    apply zzId_true in Hc. apply gz_eqb_true in Hc.
    apply zzId_true in IH. apply gz_eqb_true in IH.
    rewrite IH, <- Hc. apply zzId_from_eq. apply gz_eqb_refl.
Qed.

(* ============================================================ *)
(* §3 字面锚（红笔③ norm 档 20/40/5＋除法自由形读出＋基座烟测）                  *)
(* ============================================================ *)

Lemma gnorm_anchor_4_2 : zzId (Z.eqb (gnorm (mkz 4 2)) 20) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gnorm_anchor_6_2 : zzId (Z.eqb (gnorm (mkz 6 2)) 40) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gnorm_anchor_m1_2 : zzId (Z.eqb (gnorm (mkz (Z.opp 1) 2)) 5) true.
Proof. vm_compute. reflexivity. Qed.

(* 除法自由形读出锚：Im[(4+2i)^{−1}] = −2/20（读出位 Qmake·Qdiv 形） *)
Lemma gz_im_neg_frac_anchor_4_1 :
  zzId (Qeq_bool (((fst (gz_im_neg_frac (mkz 4 2) 1)) # 1) /
                  ((snd (gz_im_neg_frac (mkz 4 2) 1)) # 1))%Q
                  ((-2) # 20)%Q) true.
Proof. vm_compute. reflexivity. Qed.

(* 基座烟测：减法/幂/共轭幂复合一发：Im[(−1+2i)³]=−2·Im[(−1−2i)³]=+2 的对偶面 *)
Lemma gz_pow_anchor_m1_2_3 :
  zzId (gz_eqb (gz_pow (mkz (Z.opp 1) 2) 3) (mkz 11 (Z.opp 2))) true.
Proof. vm_compute. reflexivity. Qed.

Lemma gz_sub_anchor : zzId (gz_eqb (gz_sub (mkz 5 3) (mkz 2 1)) (mkz 3 2)) true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §4 审计（零全局假设复核）                                                     *)
(* ============================================================ *)

Print Assumptions gz_im_neg_frac.
Print Assumptions gnorm_mul_b.
Print Assumptions gnorm_pow_b.
Print Assumptions gz_pow_conj_b.
Print Assumptions gnorm_anchor_4_2.
Print Assumptions gz_im_neg_frac_anchor_4_1.
