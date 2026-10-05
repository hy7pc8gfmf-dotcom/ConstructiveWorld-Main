(* ============================================================ *)
(* 模块名：abl_prop_carrier —— Prop 旗标补齐件（审计旗标 Prop 缩写补齐 sumbool/sigT Set 层伴随件） *)
(* 使命：对已交付件审计旗标逐位补齐 Set 层表示（原 Prop 定义保留为 spec 记号位，前件零源文改动）： *)
(*   ①旗标一（plm_pairwise_coprime）：补 plm_pairwise_coprime_sb，判定器   *)
(*   plm_pw_cop_bool 走逐对 gcd=1 bool 链（对角对与跨对同链受检），        *)
(*   sound／complete 双向闭合；连带主定理伴随闭式推论位                    *)
(*   plm_coprime_prod_dvd_closed（sigT：整除证书或否定数据）。             *)
(*   ②旗标二：补 plm/lcm 侧使用形 plm_prime_sb——直连 redischarge 池件     *)
(*   abl_redischarge_pr01_sb 的 pr_prime_sb（真调用重导出，非重证），附    *)
(*   lcm 侧三分闭式推论 plm_prime_gcd_1_closed（sigT/option bool 标签）。  *)
(*   ③旗标三（dsu_neg 系）：勘查已覆盖——abl_redischarge_sumd_inst 已给    *)
(*   dsu_list_ne_sb，本件如实跳过，不重复补位。                            *)
(* 依赖清单（本池拷贝链编，前件零改动）：abl_Pr_core_01 → abl_Pr_euclid_03 *)
(*   → abl_Pr_lcmdecomp_04（plm_pairwise_coprime／plm_coprime_prod_dvd／  *)
(*   plm_prime_gcd_1）→ abl_redischarge_pr01_sb（pr_prime_sb 系）→ 本件；  *)
(*   HansonLcm 经缓存根 -Q 只读引用；纯 Stdlib（Arith.Arith／List 等）。   *)
(* 构造性注记：零承认／零经典逻辑；新增语句面全 Set 表示（sumbool／sigT）， *)
(*   否定一律 P -> False 自持（本安装无 Not，全件零否定记号书写）；判定件  *)
(*   plm_pairwise_coprime_sb／plm_prime_sb 皆 Defined 出口保可提取；闭式  *)
(*   推论位 Qed（逻辑闭合位，表示仍在 sumbool）；数值烟测表长 ≤3、元素 ≤5。 *)
(* 诚实边界：宿主 plm_pairwise_coprime 为全对形（含对角 gcd x x = x），该   *)
(*   谓词仅对全 1 表为真——判定链忠实复刻宿主定义语义（对角在链内显式受检）， *)
(*   不放大不缩水；旗标三已覆盖位零触碰，不补全等式分解枚举表（宿主未竟位）。 *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB &&           *)
(*   ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q <world> ""   *)
(*   前四件依次链编后编本件（末位加 -Q <缓存根> "" -Q . ""）；绿判=EXIT=0。 *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Import ListNotations.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_redischarge_pr01_sb.

(* ---- §1 旗标一：plm_pairwise_coprime 的 sumbool 判定伴随 ---- *)

(* §1.0 forallb 与 In 的双向小桥（stdlib List.forallb_forall 在册可查，
   自建双向引理保本件自足零外部的狭） *)
Lemma plm_forallb_in_elim : forall (f : nat -> bool) (l : list nat),
  forallb f l = true -> forall y : nat, In y l -> f y = true.
Proof.
  intros f l. induction l as [| x t IH]; simpl; intros Hb y Hy.
  - destruct Hy.
  - apply andb_prop in Hb. destruct Hb as [Hx Ht].
    destruct Hy as [Hy | Hy].
    + rewrite <- Hy. exact Hx.
    + exact (IH Ht y Hy).
Qed.

Lemma plm_forallb_in_intro : forall (f : nat -> bool) (l : list nat),
  (forall y : nat, In y l -> f y = true) -> forallb f l = true.
Proof.
  intros f l. induction l as [| x t IH]; simpl; intros H.
  - reflexivity.
  - apply andb_true_intro. split.
    + apply H. apply in_eq.
    + apply IH. intros y Hy. apply H. apply in_cons. exact Hy.
Qed.

(* §1.1 判定器：逐对 gcd=1 bool 链——头部 x 对全表（x::t）forallb：
   对角对（y=x）与跨对（y 属 t）同链受检；尾段递归。
   宿主定义含全对（x=y 在内），故对角必须在链内，sound 才能闭合。 *)
Fixpoint plm_pw_cop_bool (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: t =>
      forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t) && plm_pw_cop_bool t
  end.

(* §1.2 sound：读数 true ⟹ 两两互素证书。
   a=x 肢：forallb 直供；a 异 x、b=x 肢：forallb＋gcd 交换律回供；
   双双入尾肢：归纳（Hpt）。 *)
Lemma plm_pw_cop_bool_sound : forall l : list nat,
  plm_pw_cop_bool l = true -> plm_pairwise_coprime l.
Proof.
  intros l. induction l as [| x t IH]; intros Hbool a b Ha Hbin.
  - simpl in Ha. destruct Ha.
  - change (plm_pw_cop_bool (x :: t))
      with (forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t)
            && plm_pw_cop_bool t) in Hbool.
    apply andb_prop in Hbool. destruct Hbool as [Hall Ht].
    assert (Hpt : plm_pairwise_coprime t) by (apply IH; exact Ht).
    assert (Hx : forall y : nat, In y (x :: t) -> Nat.gcd x y = 1)
      by (intros y Hy;
          apply (proj1 (Nat.eqb_eq (Nat.gcd x y) 1));
          exact (plm_forallb_in_elim _ _ Hall y Hy)).
    destruct (Nat.eq_dec a x) as [Ea | Na].
    + rewrite Ea. exact (Hx b Hbin).
    + assert (Hat : In a t).
      { destruct Ha as [Ha' | Ha'].
        - exfalso. apply Na. rewrite Ha'. reflexivity.
        - exact Ha'. }
      destruct (Nat.eq_dec b x) as [Eb | Nb].
      * assert (Hax : In a (x :: t)) by (apply in_cons; exact Hat).
        rewrite Eb. rewrite (Nat.gcd_comm a x). exact (Hx a Hax).
      * apply Hpt; [exact Hat |].
        destruct Hbin as [Hbin' | Hbin'].
        -- exfalso. apply Nb. rewrite Hbin'. reflexivity.
        -- exact Hbin'.
Qed.

(* §1.3 complete：证书 ⟹ 读数 true——对角肢＝证书自对（in_eq）直供，
   跨对肢＝证书全对直供，尾段＝逐对弱化（in_cons）。 *)
Lemma plm_pw_cop_bool_complete : forall l : list nat,
  plm_pairwise_coprime l -> plm_pw_cop_bool l = true.
Proof.
  intros l. induction l as [| x t IH]; intros Hpw.
  - reflexivity.
  - unfold plm_pairwise_coprime in Hpw.
    change (plm_pw_cop_bool (x :: t))
      with (forallb (fun y => Nat.eqb (Nat.gcd x y) 1) (x :: t)
            && plm_pw_cop_bool t).
    apply andb_true_intro. split.
    + apply plm_forallb_in_intro. intros y Hy.
      apply (proj2 (Nat.eqb_eq (Nat.gcd x y) 1)).
      apply Hpw; [apply in_eq | exact Hy].
    + apply IH. intros a b Ha Hbin.
      apply Hpw; [apply in_cons; exact Ha | apply in_cons; exact Hbin].
Qed.

(* §1.4 否定自持（P -> False 原定义形，本安装无 Not）＋sumbool 判定
   伴随（Set 表示；Defined 出口保可提取——真消解，非折算件） *)
Definition plm_pairwise_coprime_neg (l : list nat) : Prop :=
  plm_pairwise_coprime l -> False.

Definition plm_pairwise_coprime_sb (l : list nat) :
  {plm_pairwise_coprime l} + {plm_pairwise_coprime_neg l}.
Proof.
  destruct (plm_pw_cop_bool l) eqn:E.
  - apply left. exact (plm_pw_cop_bool_sound l E).
  - apply right. intros Hpw.
    assert (Hb : plm_pw_cop_bool l = true)
      by exact (plm_pw_cop_bool_complete l Hpw).
    rewrite E in Hb. discriminate Hb.
Defined.

(* §1.5 消解面：判定件与 bool 机读数一致（使用方零损失换形） *)
Theorem plm_pairwise_coprime_sb_mirror : forall l : list nat,
  match plm_pairwise_coprime_sb l with
  | left _ => plm_pw_cop_bool l = true
  | right _ => plm_pw_cop_bool l = false
  end.
Proof.
  intros l. destruct (plm_pairwise_coprime_sb l) as [Hpw | Hneg].
  - exact (plm_pw_cop_bool_complete l Hpw).
  - destruct (plm_pw_cop_bool l) eqn:E.
    + exfalso. exact (Hneg (plm_pw_cop_bool_sound l E)).
    + reflexivity.
Qed.

(* §1.6 主定理伴随闭式推论位：逐点整除在手，判定件左肢经主定理
   收出整除证书，右肢出否定数据——sigT 式全 Set 表示闭式 *)
Theorem plm_coprime_prod_dvd_closed : forall (l : list nat) (c : nat),
  (forall x : nat, In x l -> Nat.divide x c) ->
  {Nat.divide (fold_right Nat.mul 1 l) c} + {plm_pairwise_coprime_neg l}.
Proof.
  intros l c Hdiv. destruct (plm_pairwise_coprime_sb l) as [Hpw | Hneg].
  - apply left. exact (plm_coprime_prod_dvd l c Hdiv Hpw).
  - apply right. exact Hneg.
Qed.

(* ---- §2 旗标二：pr_prime 系的 plm/lcm 侧使用形 ---- *)

(* 直连 redischarge 池件 pr01_sb 的 pr_prime_sb／pr_prime_neg：
   plm 侧重导出（真调用，非重证；透明直定义保可提取透传） *)
Definition plm_prime_sb (p : nat) : {pr_prime p} + {pr_prime_neg p} :=
  pr_prime_sb p.

(* 读数一致性（透传 pr_prime_sb_mirror） *)
Theorem plm_prime_sb_mirror : forall p : nat,
  match plm_prime_sb p with
  | left _ => pr_prime_bool p = true
  | right _ => pr_prime_bool p = false
  end.
Proof. intros p. exact (pr_prime_sb_mirror p). Qed.

(* lcm 侧闭式推论位：双判定件＋相异前提 ⟹ 三分闭式（sigT 承载，
   option bool 标签：None 肢=gcd 证书；Some true=对 p 的否定数据；
   Some false=对 q 的否定数据——真调用宿主 plm_prime_gcd_1） *)
Theorem plm_prime_gcd_1_closed : forall p q : nat,
  (p = q -> False) ->
  {e : option bool &
    match e with
    | None => Nat.gcd p q = 1
    | Some true => pr_prime_neg p
    | Some false => pr_prime_neg q
    end}.
Proof.
  intros p q Hne. destruct (plm_prime_sb p) as [Hp | Hnp].
  - destruct (plm_prime_sb q) as [Hq | Hnq].
    + exists None. exact (plm_prime_gcd_1 p q Hp Hq Hne).
    + exists (Some false). exact Hnq.
  - exists (Some true). exact Hnp.
Qed.

(* ---- §3 数值定装烟测（小实例 vm_compute 直算零公设；表长 ≤3、     *)
(*   元素 ≤5） ---- *)

(* 旗标一判定读数：空表／全 1 表左肢；含 2 元素表右肢
   （宿主全对定义含对角的忠实直算实证） *)
Lemma plm_pw_sb_empty :
  match plm_pairwise_coprime_sb (@nil nat) with
  | left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_pw_sb_1 :
  match plm_pairwise_coprime_sb (1 :: nil) with
  | left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_pw_sb_11 :
  match plm_pairwise_coprime_sb (1 :: 1 :: nil) with
  | left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_pw_sb_23 :
  match plm_pairwise_coprime_sb (2 :: 3 :: nil) with
  | left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_pw_sb_235 :
  match plm_pairwise_coprime_sb (2 :: 3 :: 5 :: nil) with
  | left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

(* 旗标二判定读数透传可算实证 *)
Lemma plm_prime_sb_7 :
  match plm_prime_sb 7 with left _ => true | right _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_prime_sb_8 :
  match plm_prime_sb 8 with left _ => true | right _ => false end = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- §4 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions plm_forallb_in_elim.
Print Assumptions plm_forallb_in_intro.
Print Assumptions plm_pw_cop_bool_sound.
Print Assumptions plm_pw_cop_bool_complete.
Print Assumptions plm_pairwise_coprime_sb.
Print Assumptions plm_pairwise_coprime_sb_mirror.
Print Assumptions plm_coprime_prod_dvd_closed.
Print Assumptions plm_prime_sb.
Print Assumptions plm_prime_sb_mirror.
Print Assumptions plm_prime_gcd_1_closed.
Print Assumptions plm_pw_sb_235.
Print Assumptions plm_prime_sb_8.
