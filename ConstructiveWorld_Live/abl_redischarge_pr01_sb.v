(* ============================================================ *)
(* 模块名：abl_redischarge_pr01_sb —— 再次消解件 5：abl_Pr_core_01  *)
(*   Set 层升级                                                    *)
(* 使命：前件 abl_Pr_core_01 的素性谓词 pr_prime : nat -> Prop     *)
(*   原文保留（spec 记号位）；本件增 sumbool 判定伴随              *)
(*   pr_prime_sb : forall n, {pr_prime n} + {pr_prime_neg n}      *)
(*   （pr_prime_neg n := pr_prime n -> False：否定以 P->False      *)
(*   自持——本安装无 Not，照先例零 not/~/<> 书写），使判定          *)
(*   主形落 Set（sumbool 为 Set 类；由 pr_prime_bool 反射构造，     *)
(*   Defined 出口保可提取——消解后判定读数可直接 vm_compute）。     *)
(* 依赖清单：前件 abl_Pr_core_01（本池拷贝链编：pr_prime／           *)
(*   pr_prime_bool／pr_prime_bool_true／pr_prime_bool_false）；     *)
(*   纯 Stdlib sumbool（{P}+{Q} 记号）。零新增公理面。              *)
(* 构造性注记：零承认／零经典逻辑／语句面全 Set（sumbool 表示）；    *)
(*   pr_prime_sb 体只做 bool 分支消去（真消解，非折算件）；          *)
(*   数值烟测走小实例 vm_compute（≤12）。                           *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB &&    *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler  *)
(*   no -Q <world> "" abl_Pr_core_01.v（先）&& 同配方编本件（后）。  *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.

(* ---- §1 否定词自持（本安装无 Not；P -> False 原定义形） ---- *)

Definition pr_prime_neg (n : nat) : Prop := pr_prime n -> False.

(* ---- §2 判定伴随：sumbool 表示（Set 类），由 pr_prime_bool 反射 ---- *)
(*   左肢：读数 true ⟹ 素证书（pr_prime_bool_true 直引）；            *)
(*   右肢：素 ⟹ 读数必 true，与 false 读数撞（discriminate）。        *)
(*   Defined：外层 match 只取构造子，提取面保真。                      *)
Definition pr_prime_sb (n : nat) : {pr_prime n} + {pr_prime_neg n}.
Proof.
  destruct (pr_prime_bool n) eqn:E.
  - apply left. exact (pr_prime_bool_true n E).
  - apply right. intros Hpp.
    assert (Hb : pr_prime_bool n = true)
      by exact (pr_prime_bool_false n Hpp).
    rewrite E in Hb. discriminate Hb.
Defined.

(* ---- §3 消解面：判定件与布尔机读数一致 ---- *)
(*   左肢 ⟹ 读数 true；右肢 ⟹ 读数 false——使用方零损失换形。       *)
Theorem pr_prime_sb_mirror : forall n : nat,
  match pr_prime_sb n with
  | left _ => pr_prime_bool n = true
  | right _ => pr_prime_bool n = false
  end.
Proof.
  intros n. destruct (pr_prime_sb n) as [Hp | Hn].
  - exact (pr_prime_bool_false n Hp).
  - destruct (pr_prime_bool n) eqn:E.
    + exact (False_ind _ (Hn (pr_prime_bool_true n E))).
    + reflexivity.
Qed.

(* ---- §4 判定读数的 Prop 衣（判定主形仍在 §2 sumbool，本件仅       *)
(*   便于既有 Prop 使用位换形；双肢皆由判定件直供） ---- *)
Definition pr_prime_sb_prop (n : nat) : Prop :=
  match pr_prime_sb n with
  | left _ => pr_prime n
  | right _ => pr_prime_neg n
  end.

Theorem pr_prime_sb_prop_holds : forall n : nat, pr_prime_sb_prop n.
Proof.
  intros n. unfold pr_prime_sb_prop.
  destruct (pr_prime_sb n) as [Hp | Hn].
  - exact Hp.
  - exact Hn.
Qed.

(* ---- §5 数值定装烟测（小实例 ≤ 12，vm_compute 直算零公设；         *)
(*   pr_prime_sb Defined 出口使判定读数可计算——Set 层升级实证）      *)
Lemma pr_prime_sb_2 : match pr_prime_sb 2 with left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_3 : match pr_prime_sb 3 with left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_4 : match pr_prime_sb 4 with left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_5 : match pr_prime_sb 5 with left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_9 : match pr_prime_sb 9 with left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_11 : match pr_prime_sb 11 with left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_12 : match pr_prime_sb 12 with left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- §6 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions pr_prime_sb.
Print Assumptions pr_prime_sb_mirror.
Print Assumptions pr_prime_sb_prop_holds.
Print Assumptions pr_prime_sb_2.
Print Assumptions pr_prime_sb_12.
