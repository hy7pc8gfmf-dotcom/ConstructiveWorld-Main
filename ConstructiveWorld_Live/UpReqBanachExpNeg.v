(* ============================================================ *)
(* UpReqBanachExpNeg.v —— 路径 B exp_neg 元素化件                  *)
(* ============================================================ *)
(* ============================================================ *)
(* 使命：S4 可逆性 (e^a)^{-1}=e^{-a} 的前置面——exp 在 bopp a 处   *)
(* 的元素化，并把上层数学要引用的面备齐。                         *)
(*                                                             *)
(* 路线判定（按源码实形勘定）：                                    *)
(*   B25 件出口 bxdef_exp/bxdef_exp_spec(_eps) 为全参数化形       *)
(*   （forall B a，类字段 @ 显式），把 a 换成 @bopp B a 即零新证   *)
(*   直引——主件 bxn_exp_neg 为 bxdef_exp 于 (bopp a) 实例化的     *)
(*   一行直构，收敛规格为 bxdef_exp_spec 同位转引（零新证）。      *)
(*   Class 无 bneg 类字段——(−1)^k 载体按 bmult (bopp bone) 路线   *)
(*   实测定形：bpow (bopp bone) 偶次 bae bone、奇次               *)
(*   bae (bopp bone)（bxn_mone_sq 分配展开链 + 双步归纳）。        *)
(*                                                             *)
(* 复用声明：Require Import UpReqBanachExp + UpReqBanachExpDef，  *)
(*   bxdef_exp/bxdef_exp_spec(_eps)/exp_series_partial/bpow/      *)
(*   bopp/bnorm_opp/bnorm_bpow/bae 家族全部原样复用，零重定义。    *)
(*                                                             *)
(* 红线自审：语句面全 Set 层（blim/bae/QltT/QleT'/Id/sigT 均为    *)
(*   既有 Set 承载面）；本件无新增泄露面、无经典依赖、无承认件；   *)
(*   G1 禁词口径全文件（含注释）零字面量。                         *)
(* 编译配方：SW2 全字面环境（COQLIB/ROCQLIB/OCAMLLIB/COQPATH 置空）， *)
(*   Rocq 9.1 coqc -q -native-compiler no，-Q 单根。 *)
(*                                                             *)
(* 未消解项（如实）：S4 可逆性本体（(e^a)^{-1}=e^{-a}）需 exp_add *)
(*   装配（BA/BT/BNC 上游齐备后另行闭合），本件只备 exp_neg 元素 + *)
(*   收敛规格 + 范数面 + 符号交错定形；符号交错级数的正性面        *)
(*   不在本件范围。exp_neg(0)=bone 的完全等式面同为上游件未消解项*)
(*   （接口位缺「范数任意小推 bae bzero」），本件交邻域面。        *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S2 主件：exp_neg 元素（bxdef_exp 于 bopp a 实例化）+ 收敛规格   *)
(* ============================================================ *)

(* exp_neg 元素定义：exp 在加法逆元处的取值（一行直构）。          *)
Definition bxn_exp_neg (B : BanachAlg) (a : (@BA B)) : (@BA B) :=
  bxdef_exp B (@bopp B a).

(* 收敛规格（零新证转引）：exp_neg 是 bopp a 处级数部分和的极限。  *)
Lemma bxn_exp_neg_spec : forall (B : BanachAlg) (a : (@BA B)),
  blim B (fun n => exp_series_partial B (@bopp B a) n) (bxn_exp_neg B a).
Proof.
  intros B a. exact (bxdef_exp_spec B (@bopp B a)).
Qed.

(* 收敛规格的 eps/N 展开形（下游免再 destruct 的便利面，同 B25）。 *)
Lemma bxn_exp_neg_spec_eps : forall (B : BanachAlg) (a : (@BA B)) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall n : nat,
    NatLe N n ->
    QltT (@bnorm B (@bplus B (exp_series_partial B (@bopp B a) n)
                              (@bopp B (bxn_exp_neg B a)))) eps).
Proof.
  intros B a eps Heps. exact (bxdef_exp_spec_eps B (@bopp B a) eps Heps).
Qed.

(* ============================================================ *)
(* S1 系列面：bopp a 处级数的形态定形                              *)
(* （Class 无 bneg 类字段——(−1)^k 载体取 bmult (bopp bone) 路线：  *)
(*   偶次 bae bone、奇次 bae (bopp bone)，符号交错定位。）         *)
(* ============================================================ *)

(* 负单位平方：bmult (bopp bone) (bopp bone) bae bone。            *)
(* （bopp_unique 于「单位逆 + 乘积 ≡ 0」：分配展开 + 单位清边。）   *)
Lemma bxn_mone_sq : forall (B : BanachAlg),
  @bae B (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B))) (@bone B).
Proof.
  intros B.
  eapply bae_trans.
  { apply (@bopp_unique B
        (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
        (@bopp B (@bone B))).
    (* bplus (乘积) (bopp bone) bae bzero *)
    eapply bae_trans.
    { exact (@bplus_comm B (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                           (@bopp B (@bone B))). }
    eapply bae_trans.
    { exact (@bae_sym B _ _
        (@bae_trans B _ _ _
          (@bdistrib_l B (@bopp B (@bone B)) (@bone B) (@bopp B (@bone B)))
          (@bplus_wd B (@bmult B (@bopp B (@bone B)) (@bone B))
                       (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                       (@bopp B (@bone B))
                       (@bmult B (@bopp B (@bone B)) (@bopp B (@bone B)))
                       (@bmult_one_r B (@bopp B (@bone B)))
                       (@bae_refl B (@bmult B (@bopp B (@bone B))
                                              (@bopp B (@bone B))))))). }
    eapply bae_trans.
    { exact (@bmult_wd B (@bopp B (@bone B))
                         (@bplus B (@bone B) (@bopp B (@bone B)))
                         (@bopp B (@bone B)) (@bzero B)
                         (@bae_refl B (@bopp B (@bone B)))
                         (@bplus_opp B (@bone B))). }
    exact (@bmult_zero B (@bopp B (@bone B))).
  }
  exact (@bae_sym B _ _
    (@bopp_unique B (@bone B) (@bopp B (@bone B)) (@bplus_opp B (@bone B)))).
Qed.

(* 双步自然数（偶次序载体；库内自定义，避开 stdlib 名依赖）。      *)
Fixpoint bxn_double (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | Datatypes.S m => Datatypes.S (Datatypes.S (bxn_double m))
  end.

(* 符号交错偶次面：bpow (bopp bone) (bxn_double k) bae bone。      *)
Lemma bxn_series_mone_even : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bone B)) (bxn_double k)) (@bone B).
Proof.
  intros B k. induction k as [| j IHj].
  - exact (@bae_refl B (@bone B)).
  - change (bxn_double (Datatypes.S j))
      with (Datatypes.S (Datatypes.S (bxn_double j))).
    change (bpow B (@bopp B (@bone B))
                   (Datatypes.S (Datatypes.S (bxn_double j))))
      with (@bmult B (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double j))
                               (@bopp B (@bone B)))
                     (@bopp B (@bone B))).
    eapply bae_trans.
    { exact (@bmult_wd B
          (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double j))
                   (@bopp B (@bone B)))
          (@bopp B (@bone B))
          (@bmult B (@bone B) (@bopp B (@bone B))) (@bopp B (@bone B))
          (@bmult_wd B (bpow B (@bopp B (@bone B)) (bxn_double j))
                       (@bopp B (@bone B))
                       (@bone B) (@bopp B (@bone B))
                       IHj (@bae_refl B (@bopp B (@bone B))))
          (@bae_refl B (@bopp B (@bone B)))). }
    eapply bae_trans.
    { exact (@bmult_wd B (@bmult B (@bone B) (@bopp B (@bone B)))
                        (@bopp B (@bone B))
                        (@bopp B (@bone B)) (@bopp B (@bone B))
                        (@bmult_one_l B (@bopp B (@bone B)))
                        (@bae_refl B (@bopp B (@bone B)))). }
    exact (bxn_mone_sq B).
Qed.

(* 符号交错奇次面：bpow (bopp bone) (S (bxn_double k))             *)
(*   bae (bopp bone)。                                            *)
Lemma bxn_series_mone_odd : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bone B)) (Datatypes.S (bxn_double k)))
        (@bopp B (@bone B)).
Proof.
  intros B k.
  change (bpow B (@bopp B (@bone B)) (Datatypes.S (bxn_double k)))
    with (@bmult B (bpow B (@bopp B (@bone B)) (bxn_double k))
                   (@bopp B (@bone B))).
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bopp B (@bone B)) (bxn_double k))
                      (@bopp B (@bone B))
                      (@bone B) (@bopp B (@bone B))
                      (bxn_series_mone_even B k)
                      (@bae_refl B (@bopp B (@bone B)))). }
  exact (@bmult_one_l B (@bopp B (@bone B))).
Qed.

(* ============================================================ *)
(* S3 加分：范数面（S4 尾界复用）+ exp_neg(0) 邻域面               *)
(* ============================================================ *)

(* 范数面出口：‖bopp a‖ == ‖a‖（Class 字段具名引出，S4 尾界直引）。 *)
Lemma bxn_bnorm_opp : forall (B : BanachAlg) (a : (@BA B)),
  Id (@bnorm B (@bopp B a)) (@bnorm B a).
Proof.
  intros B a. exact (@bnorm_opp B a).
Qed.

(* 幂范数面：‖(bopp a)^k‖ ≤T ‖a‖^k（尾界在 bopp a 处同界复用）。   *)
Lemma bxn_bnorm_bpow_opp : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  QleT' (@bnorm B (bpow B (@bopp B a) k)) (q_pow (@bnorm B a) k).
Proof.
  intros B a k.
  rewrite <- (@bnorm_opp B a).
  exact (bnorm_bpow B (@bopp B a) k).
Qed.

(* 负零面：bopp bzero bae bzero（单位消 + 加法逆两步）。           *)
Lemma bxn_opp_bzero : forall (B : BanachAlg),
  @bae B (@bopp B (@bzero B)) (@bzero B).
Proof.
  intros B.
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_zero B (@bopp B (@bzero B)))). }
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_comm B (@bzero B) (@bopp B (@bzero B)))). }
  exact (@bplus_opp B (@bzero B)).
Qed.

(* 负零幂尾：bpow (bopp bzero) (S k) bae bzero。                   *)
Lemma bxn_bpow_opp_zero_tail : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bopp B (@bzero B)) (Datatypes.S k)) (@bzero B).
Proof.
  intros B k. induction k as [| j IHj].
  - change (bpow B (@bopp B (@bzero B)) (Datatypes.S 0%nat))
      with (@bmult B (@bone B) (@bopp B (@bzero B))).
    eapply bae_trans.
    { exact (@bmult_one_l B (@bopp B (@bzero B))). }
    exact (bxn_opp_bzero B).
  - change (bpow B (@bopp B (@bzero B)) (Datatypes.S (Datatypes.S j)))
      with (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S j))
                     (@bopp B (@bzero B))).
    eapply bae_trans.
    { exact (@bmult_wd B (bpow B (@bopp B (@bzero B)) (Datatypes.S j))
                        (@bopp B (@bzero B))
                        (@bzero B) (@bzero B)
                        IHj (bxn_opp_bzero B)). }
    exact (@bmult_zero B (@bzero B)).
Qed.

(* 负零级数项退化：负零幂 × 系数 bae bzero。                       *)
Lemma bxn_esp_term_opp_zero : forall (B : BanachAlg) (k : nat) (q : Q),
  @bae B (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S k))
                   (@bcoef B q))
        (@bzero B).
Proof.
  intros B k q.
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bopp B (@bzero B)) (Datatypes.S k))
                      (@bcoef B q)
                      (@bzero B) (@bcoef B q)
                      (bxn_bpow_opp_zero_tail B k)
                      (@bae_refl B (@bcoef B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm B q (@bzero B)). }
  exact (@bmult_zero B (@bcoef B q)).
Qed.

(* exp_neg(0) 部分和恒一：esp (bopp bzero) n bae bone。            *)
(* （对接 BXB 的 bxb_series_zero 同族面：负零处级数列同退化。）     *)
Lemma bxn_series_opp_zero : forall (B : BanachAlg) (n : nat),
  @bae B (exp_series_partial B (@bopp B (@bzero B)) n) (@bone B).
Proof.
  intros B n. induction n as [| m IHm].
  - change (exp_series_partial B (@bopp B (@bzero B)) 0%nat) with (@bone B).
    exact (@bae_refl B (@bone B)).
  - change (exp_series_partial B (@bopp B (@bzero B)) (Datatypes.S m))
      with (@bplus B (exp_series_partial B (@bopp B (@bzero B)) m)
              (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S m))
                        (@bcoef B (/ q_fact (Datatypes.S m))))).
    eapply bae_trans.
    { exact (@bplus_wd B (exp_series_partial B (@bopp B (@bzero B)) m)
                        (@bmult B (bpow B (@bopp B (@bzero B)) (Datatypes.S m))
                                  (@bcoef B (/ q_fact (Datatypes.S m))))
                        (@bone B) (@bzero B)
                        IHm
                        (bxn_esp_term_opp_zero B m
                           (/ q_fact (Datatypes.S m)))). }
    exact (@bplus_zero B (@bone B)).
Qed.

(* exp_neg(0) 极限邻域面：bone 与 exp_neg(bzero) 范数任意贴近。     *)
(* （完全等式面被「范数任意小推 bae bzero」接口位缺失挡住——         *)
(*   承上游件同源未消解项，不作无依据凑形。）                      *)
Lemma bxn_exp_neg_zero_close : forall (B : BanachAlg) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm B (@bplus B (@bone B)
                           (@bopp B (bxn_exp_neg B (@bzero B))))) eps.
Proof.
  intros B eps Heps.
  destruct (bxn_exp_neg_spec B (@bzero B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
  pose proof (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bopp B (@bzero B)) N)
                (@bopp B (bxn_exp_neg B (@bzero B))))
      (@bplus B (@bone B) (@bopp B (bxn_exp_neg B (@bzero B))))
      (@bplus_wd B (exp_series_partial B (@bopp B (@bzero B)) N)
                  (@bopp B (bxn_exp_neg B (@bzero B)))
                  (@bone B) (@bopp B (bxn_exp_neg B (@bzero B)))
                  (bxn_series_opp_zero B N)
                  (@bae_refl B (@bopp B (bxn_exp_neg B (@bzero B)))))) as HWn.
  exact (QeqT_Qlt_bool_cong _ _ eps HWn HN).
Qed.

(* ============================================================ *)
(* 未消解项申报（对称，不落承认件）：                              *)
(*   ① S4 可逆性本体（(e^a)^{-1}=e^{-a}）：需 exp_add 装配         *)
(*      （BA/BT/BNC 产出后另席）；本件已备齐其前置引用面：          *)
(*      bxn_exp_neg（元素）+ bxn_exp_neg_spec(_eps)（收敛规格）     *)
(*      + bxn_bnorm_opp/bxn_bnorm_bpow_opp（范数面）                *)
(*      + bxn_series_mone_even/odd（符号交错定形）。                *)
(*   ② 符号交错级数的正性面：非本件范围。                               *)
(*   ③ exp_neg(0)=bone 完全等式面：同上游件未消解项（接口位缺失），*)
(*      本件交至邻域面 bxn_exp_neg_zero_close。                     *)
(* ============================================================ *)
