(* ============================================================ *)
(* UpReqEqbComplete.v —— 近似判定完备性分离的泛型母件化                *)
(*                                                              *)
(* 目的：源自库内定理景观普查候选项「近似判定完备性分离」的泛型母件化。  *)
(*   核心结论：eqb 型近似判定器的「完备性方向」（判真 ⟹ Leibniz 相等）   *)
(*   对任意判定器不可无条件成立（双实例实形均为其反例），故最强可达形     *)
(*   =分离包。                                                        *)
(*                                                              *)
(* 主件（前缀 eqc_，避免与库内既有名冲突）：                           *)
(*   §1 泛型母件（Section EqbComplete，域/判定器/尺寸测度全显式参）：    *)
(*      ①完备性成立 ⟹ gap 门闭；②gap 对逐点见证 ⟹ 完备性失效；          *)
(*      ③合取装配形；④⑤桥测度守恒（gap 对过保测桥尺寸逐点重合＋         *)
(*      反例门恒开）；⑥⑦Set 层显式见证器（sigT 信息性数据包，bool        *)
(*      证书与数值测度存活于提取面，不等门 Prop 位提取擦除——             *)
(*      is_num_size1_set / ev_append_size_set 同款定式）。              *)
(*   §2 双实例逐字转发（转发件=消费实证，零重复证明）：                  *)
(*      实例甲 DTPT_Truth ev_eqb_leibniz_gap（1#2 vs 2#4，               *)
(*      order:198 注册面，只读消费）；实例乙 DTPT_Bridge_Dig             *)
(*      dig_dec_not_eq_witness（dPair (dQ 0) (dQ 0) vs                   *)
(*      dPair (dQ 1) (dQ 0)，注册面在册，只读消费）。                    *)
(*      每实例三转发：逐字 gap 转发（exact 原件）/母件路由分离面          *)
(*      （判真＋不等两证书消费原件，分离结论由母件给出）/桥测度面         *)
(*      （乙消费 dig_dec_size 零重复；甲侧 ev_eqb 判真保尺寸面           *)
(*      在库无现成件，为本件母件化新增消费面 eqc_fwd_ev_size_conserved，  *)
(*      如实记档非转发）。                                              *)
(*   §3 公理闭包审计。                                                  *)
(*                                                              *)
(* 实形校正（对上游普查报告草案）：双实例实形均为                         *)
(*   「eqb p q = true /\ p <> q」显式对合取形，非存在形；                 *)
(*   草案 eqg_gap_witness 的「Prop 存在形→sigT 升格」前提形态             *)
(*   （可判搜索）在泛型域上构造性不可达，本件以显式对合 Set 数据包        *)
(*   （⑥⑦）承接升格诉求，全件零全局假设、前提全走定理显式参。            *)
(*                                                              *)
(* 备注：公理面：全件零全局假设；件尾 Print Assumptions 闭包审计          *)
(*   预期全 Closed；提取面 Obj.magic 计数 0。                            *)
(*   红线：纯构造性收口全程 Qed；Set 层结论面（bool 等式＋nat 测度        *)
(*   ＋sigT 载体），Id/<> 失效面与两实例现件同形合法；nat 层显式           *)
(*   Datatypes.S/O 与 %nat/%Q 标注；类型位积一律显式 prod                  *)
(*   （E644 Q_scope 类型位星号劫持预防）。零改既有件。                    *)
(* ============================================================ *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List Bool Arith Lia.
Require DTPT.
Require DTPT_DigTheory.
Require DTPT_Truth.
Require DTPT_Bridge_Dig.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Truth.DTPT_Truth.
Import DTPT_Bridge_Dig.DTPT_Bridge_Dig.

(* ============================================================
   §1 泛型母件（Section 泛化：域 A / 判定器 eqb / 尺寸测度 size
   全显式参；前提全走定理显式参，零 Hypothesis 位）
   ============================================================ *)
Section EqbComplete.

  Variable A : Type.
  Variable eqb : A -> A -> bool.
  Variable size : A -> nat.

  (* 母件①（完备性方向·分离核）：若判定器完备（判真 ⟹ Leibniz
     相等），则 gap 门对任意逐点见证对闭合——完备性与反例互斥。 *)
  Theorem eqc_complete_closes_gap :
    (forall a b, eqb a b = true -> a = b) ->
    forall p q, eqb p q = true -> p <> q -> False.
  Proof.
    intros Hcom p q Hp Hne. apply Hne. apply Hcom. exact Hp.
  Qed.

  (* 母件②（反例完备性·主件）：逐点 gap 对（判真+Leibniz 失效）
   的构造性见证 ⟹ 完备性方向失效——「不可判定对的构造性见证
   与 Leibniz 相等失效等价」的可达半边（对侧即母件①）。 *)
  Theorem eqc_gap_breaks_complete :
    forall p q, eqb p q = true -> p <> q ->
    ~ (forall a b, eqb a b = true -> a = b).
  Proof.
    intros p q Hp Hne Hcom. apply Hne. apply Hcom. exact Hp.
  Qed.

  (* 母件③（分离装配形）：gap 对逐点证书 ⟹ 合取证书 + 完备性
   失效对——实例转发直用形。 *)
  Corollary eqc_separation_conj :
    forall p q, eqb p q = true -> p <> q ->
    (eqb p q = true /\ p <> q)
    /\ ~ (forall a b, eqb a b = true -> a = b).
  Proof.
    intros p q Hp Hne. split.
    - split; [ exact Hp | exact Hne ].
    - exact (eqc_gap_breaks_complete p q Hp Hne).
  Qed.

  (* 母件④（桥测度守恒）：gap 对尺寸测度相等时，过保测桥后
   双侧测度逐点重合——分离是纯 Leibniz 面，测度无损过桥。 *)
  Theorem eqc_gap_bridge_size :
    forall (B : Type) (f : A -> B) (g : B -> nat),
      (forall a, size a = g (f a)) ->
      forall p q, eqb p q = true -> size p = size q -> g (f p) = g (f q).
  Proof.
    intros B f g Hpres p q Hp Hsz.
    rewrite <- (Hpres p), <- (Hpres q), Hsz. reflexivity.
  Qed.

  (* 母件⑤（反例门恒开·桥测度守恒全形）：尺寸测度逐点非零时
   gap 对过保测桥门恒开（测度 ≥ 1）且双侧重合——镜像
   tneg_counter_size 守恒+门开双面。 *)
  Theorem eqc_gap_bridge_gate :
    forall (B : Type) (f : A -> B) (g : B -> nat),
      (forall a, size a = g (f a)) -> (forall a, (size a <> 0)%nat) ->
      forall p q, eqb p q = true -> size p = size q ->
      (Datatypes.S Datatypes.O <= g (f p))%nat /\ g (f p) = g (f q).
  Proof.
    intros B f g Hpres Hgate p q Hp Hsz.
    rewrite <- (Hpres p), <- (Hpres q). split.
    - specialize (Hgate p). lia.
    - rewrite Hsz. reflexivity.
  Qed.

  (* 母件⑥（Set 层 gap 显式见证器）：逐点判真证书+不等门 ⟹
   sigT 显式数据包——首分量携带 gap 对与 bool 证书（存活于
   提取面），不等门 Prop 位（提取擦除；is_num_size1_set 同款
   定式）。 *)
  Definition eqc_gap_set (p q : A) (Hp : eqb p q = true) (Hne : p <> q) :
    {r : prod (prod A A) bool
        & snd r = true /\ fst (fst r) <> snd (fst r)} :=
    existT _ (pair (pair p q) (eqb p q)) (conj Hp Hne).

  (* 母件⑦（Set 层桥测度显式见证器）：gap 对测度重合 ⟹
   sigT 数值见证包——测度值 n 存活于提取面，重合方程 Prop 位。 *)
  Definition eqc_gap_size_set (p q : A) (Hsz : size p = size q) :
    {n : nat & size p = n /\ size q = n} :=
    existT _ (size p) (conj eq_refl (eq_sym Hsz)).

End EqbComplete.

(* ============================================================
   §2 双实例逐字转发（转发件=消费实证，零重复证明）
   ============================================================ *)

(* ---------- 实例甲：DTPT_Truth ev_eqb（Evidence 域，1#2 vs 2#4） ---------- *)

(* 转发件甲一（逐字转发）：原定理 ev_eqb_leibniz_gap 消费实证，
   证明体零重复。 *)
Theorem eqc_fwd_ev_gap :
  ev_eqb (evNum (1#2)%Q) (evNum (2#4)%Q) = true
  /\ evNum (1#2)%Q <> evNum (2#4)%Q.
Proof. exact ev_eqb_leibniz_gap. Qed.

(* 转发件甲二（母件路由分离面）：判真+不等两证书消费原定理，
   分离结论由母件②给出——「一母两转」的甲侧主证。 *)
Theorem eqc_fwd_ev_separation :
  ~ (forall a b : Evidence, ev_eqb a b = true -> a = b).
Proof.
  exact (eqc_gap_breaks_complete Evidence ev_eqb
         (evNum (1#2)%Q) (evNum (2#4)%Q)
         (proj1 ev_eqb_leibniz_gap) (proj2 ev_eqb_leibniz_gap)).
Qed.

(* 转发件甲三（尺寸单调面·母件化新增消费面）：ev_eqb 判真 ⟹
   ev_size 逐点重合——在库无现成件（ev_eqb_true_iff 为内容同余
   非测度面），此为母件「尺寸单调」参在甲实例的实装，如实记档
   （新证非转发）。 *)
Theorem eqc_fwd_ev_size_conserved :
  forall a b : Evidence, ev_eqb a b = true -> ev_size a = ev_size b.
Proof.
  intros a. induction a as [q1 | l1 | a1 IH1 a2 IH2];
    intros [q2 | l2 | b1 b2] H; simpl in H; try discriminate H.
  - reflexivity.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2]. simpl.
    rewrite (IH1 b1 H1), (IH2 b2 H2). reflexivity.
Qed.

(* 甲侧测度非零（反例门恒开前提，消费 ev_size_pos）。 *)
Lemma eqc_fwd_ev_nz : forall a : Evidence, (ev_size a <> 0)%nat.
Proof. intros a H0. pose proof (ev_size_pos a). lia. Qed.

(* 转发件甲四（桥测度守恒全形）：母件⑤实例化——甲对过恒等桥
   门恒开且测度重合（镜像 tneg_counter_size 双面）。 *)
Theorem eqc_fwd_ev_bridge :
  (Datatypes.S Datatypes.O <= ev_size (evNum (1#2)%Q))%nat
  /\ ev_size (evNum (1#2)%Q) = ev_size (evNum (2#4)%Q).
Proof.
  exact (eqc_gap_bridge_gate Evidence ev_eqb ev_size
         Evidence (fun d => d) ev_size
         (fun _ => eq_refl) eqc_fwd_ev_nz
         (evNum (1#2)%Q) (evNum (2#4)%Q)
         (proj1 ev_eqb_leibniz_gap)
         (eqc_fwd_ev_size_conserved (evNum (1#2)%Q) (evNum (2#4)%Q)
                                    (proj1 ev_eqb_leibniz_gap))).
Qed.

(* 甲侧 Set 层显式见证包（母件⑥⑦实例化：对+bool 证书与测度值
   存活于提取面）。 *)
Definition eqc_fwd_ev_gap_set :
  {r : prod (prod Evidence Evidence) bool
      & snd r = true /\ fst (fst r) <> snd (fst r)} :=
  eqc_gap_set Evidence ev_eqb (evNum (1#2)%Q) (evNum (2#4)%Q)
    (proj1 ev_eqb_leibniz_gap) (proj2 ev_eqb_leibniz_gap).

Definition eqc_fwd_ev_size_set :
  {n : nat & ev_size (evNum (1#2)%Q) = n /\ ev_size (evNum (2#4)%Q) = n} :=
  eqc_gap_size_set Evidence ev_size
    (evNum (1#2)%Q) (evNum (2#4)%Q)
    (eqc_fwd_ev_size_conserved (evNum (1#2)%Q) (evNum (2#4)%Q)
                               (proj1 ev_eqb_leibniz_gap)).

(* ---------- 实例乙：DTPT_Bridge_Dig dig_dec（Dig 域，dPair 对） ---------- *)

(* 转发件乙一（逐字转发）：原定理 dig_dec_not_eq_witness 消费
   实证，证明体零重复。 *)
Theorem eqc_fwd_dig_gap :
  dig_dec (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0)) = true
  /\ dPair (dQ 0) (dQ 0) <> dPair (dQ 1) (dQ 0).
Proof. exact dig_dec_not_eq_witness. Qed.

(* 转发件乙二（母件路由分离面）：两证书消费原定理，分离结论由
   母件②给出——「一母两转」的乙侧主证。 *)
Theorem eqc_fwd_dig_separation :
  ~ (forall a b : Dig, dig_dec a b = true -> a = b).
Proof.
  exact (eqc_gap_breaks_complete Dig dig_dec
         (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))
         (proj1 dig_dec_not_eq_witness) (proj2 dig_dec_not_eq_witness)).
Qed.

(* 转发件乙三（桥测度守恒）：母件④实例化——测度消费盘上
   dig_dec_size（零重复），恒等桥保测。 *)
Theorem eqc_fwd_dig_bridge :
  dig_size (dPair (dQ 0) (dQ 0)) = dig_size (dPair (dQ 1) (dQ 0)).
Proof.
  exact (eqc_gap_bridge_size Dig dig_dec dig_size
         Dig (fun d => d) dig_size
         (fun _ => eq_refl)
         (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))
         (proj1 dig_dec_not_eq_witness)
         (dig_dec_size _ _ (proj1 dig_dec_not_eq_witness))).
Qed.

(* 乙侧 Set 层显式见证包（母件⑥⑦实例化）。 *)
Definition eqc_fwd_dig_gap_set :
  {r : prod (prod Dig Dig) bool
      & snd r = true /\ fst (fst r) <> snd (fst r)} :=
  eqc_gap_set Dig dig_dec (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))
    (proj1 dig_dec_not_eq_witness) (proj2 dig_dec_not_eq_witness).

Definition eqc_fwd_dig_size_set :
  {n : nat & dig_size (dPair (dQ 0) (dQ 0)) = n
            /\ dig_size (dPair (dQ 1) (dQ 0)) = n} :=
  eqc_gap_size_set Dig dig_size
    (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))
    (dig_dec_size _ _ (proj1 dig_dec_not_eq_witness)).

(* ============================================================
   §3 提取出口 + 公理闭包审计
   ============================================================ *)

Set Extraction Output Directory ".".
Extraction "_tq19s_eqc_gap_ext.ml" eqc_fwd_ev_gap_set eqc_fwd_ev_size_set
  eqc_fwd_dig_gap_set eqc_fwd_dig_size_set.

Print Assumptions eqc_complete_closes_gap.
Print Assumptions eqc_gap_breaks_complete.
Print Assumptions eqc_separation_conj.
Print Assumptions eqc_gap_bridge_size.
Print Assumptions eqc_gap_bridge_gate.
Print Assumptions eqc_fwd_ev_gap.
Print Assumptions eqc_fwd_ev_separation.
Print Assumptions eqc_fwd_ev_size_conserved.
Print Assumptions eqc_fwd_ev_bridge.
Print Assumptions eqc_fwd_ev_gap_set.
Print Assumptions eqc_fwd_ev_size_set.
Print Assumptions eqc_fwd_dig_gap.
Print Assumptions eqc_fwd_dig_separation.
Print Assumptions eqc_fwd_dig_bridge.
Print Assumptions eqc_fwd_dig_gap_set.
Print Assumptions eqc_fwd_dig_size_set.
