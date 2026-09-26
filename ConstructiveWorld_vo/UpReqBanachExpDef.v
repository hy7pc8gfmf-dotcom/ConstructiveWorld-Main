(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bxdef_exp_spec_eps（原 L66，2 句玩具证）                             *)
(*   bxdef_exp_spec（原 L59，2 句玩具证）                                 *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 参数位＋恒等守恒 2 参数位；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBanachExpDef.v —— 席B25：路径 B S2.5 exp 元素定义席      *)
(* （20260912；后台独立席位，独占 CoreN 0）                      *)
(* ============================================================ *)
(* 使命：UpReqBanachExp.v 已证级数柯西性（exp_series_cauchy），  *)
(* 但 exp 元素本身未定义。本件把柯西性变成元素：                 *)
(*   定义 exp 元素（经 Class 完备性字段见证形）+ 收敛规格。       *)
(*                                                             *)
(* 路线判定（第一步侦察实形后裁决，报告同步）：                  *)
(*   完备性字段 bcauchy_complete 实形 = 见证形——                *)
(*     is_cauchy u -> sigT (fun l : BA => blim u l)，            *)
(*   且 UpReqBanachExp 已备具名桥 bcauchy_complete_sig          *)
(*   （bcauchy -> sigT (fun l => blim u l)，exact 直连字段）。    *)
(*   ⟹ 路线甲成立：bxdef_exp := projT1（字段见证），             *)
(*   收敛规格 blim 面一步 projT2，无需路线乙降档（无降档红线）。  *)
(*   （converges_to 对应库内具名形 blim；is_cauchy 对应 bcauchy。）*)
(*                                                             *)
(* 复用声明：Require Import UpReqBanachExp，bcauchy/blim/        *)
(*   bcauchy_complete_sig/exp_series_partial/bpow/               *)
(*   exp_series_cauchy/bae 家族全部原样复用，零重定义。          *)
(*                                                             *)
(* 红线自审：语句面全 Set 层——blim/bcauchy/QltT/bae 均为         *)
(*   UpReqBanachExp/S02 既有 Set 承载面（S02 L64-93 在案）；     *)
(*   本件无新增 Prop 泄露、无经典公理依赖、无承认件；            *)
(*   G1 禁词口径八词全文件（含注释）零字面量。                   *)
(*                                                             *)
(* 遗留（如实）：S3 exp_add（e^{a+b}=e^a·e^b）与 S4 可逆性       *)
(*   不属本席（依赖闭包见 UpReqBanachExp 文件尾登记）。          *)
(*   exp(0)=bone 的 bae 完全等式面被 Class 缺反可分性字段挡住    *)
(*   （由「范数任意小推 bae 零」不可达，见本件尾遗留注），       *)
(*   本件交至其邻域面：零元部分和恒一 + 极限范数任意贴近 one。    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S2.5 主面：exp 元素（完备性字段见证形，路线甲）               *)
(* ============================================================ *)

(* 元素+证书封装：柯西级数序列经完备性字段直接取得              *)
(*   （BISH 式「柯西序列即元素」的字段化落位——见证成对取出）。   *)
Definition bxdef_exp_pair (B : BanachAlg) (a : (@BA B)) :
  sigT (fun l : (@BA B) => blim B (fun n => exp_series_partial B a n) l) :=
  bcauchy_complete_sig B (fun n => exp_series_partial B a n)
    (exp_series_cauchy B a).

(* exp 元素定义：见证之元素半（projT1）。                       *)
(* 「定义即算法」：右端含 exp_series_partial 结构递归函数实参，  *)
(*   提取产物含级数部分和 Fixpoint（G3 佐证，报告存照）。        *)
Definition bxdef_exp (B : BanachAlg) (a : (@BA B)) : (@BA B) :=
  projT1 (bxdef_exp_pair B a).

(* 收敛规格：exp 元素是级数部分和序列的极限（blim 面一步 projT2）。 *)
Lemma bxdef_exp_spec : forall (B : BanachAlg) (a : (@BA B)),
  blim B (fun n => exp_series_partial B a n) (bxdef_exp B a).
Proof.
  intros B a.
  exact (projT2 (bxdef_exp_pair B a)).
Qed.

(* 规格的 eps/N 展开形（免 later-use 再 destruct 的便利面） *)
Lemma bxdef_exp_spec_eps : forall (B : BanachAlg) (a : (@BA B)) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall n : nat,
    NatLe N n ->
    QltT (@bnorm B (@bplus B (exp_series_partial B a n)
                              (@bopp B (bxdef_exp B a)))) eps).
Proof.
  intros B a eps Heps.
  exact (bxdef_exp_spec B a eps Heps).
Qed.

(* ============================================================ *)
(* S3 加分（起步面）：exp(0) —— 部分和恒一 + 极限范数贴 one      *)
(* ============================================================ *)

(* 零元幂尾：bpow bzero (S k) ≡ bzero（bae 等词面归纳） *)
Lemma bxdef_bpow_zero_tail : forall (B : BanachAlg) (k : nat),
  @bae B (bpow B (@bzero B) (Datatypes.S k)) (@bzero B).
Proof.
  intros B k. induction k as [| j IHj].
  - change (bpow B (@bzero B) (Datatypes.S 0%nat))
      with (@bmult B (@bone B) (@bzero B)).
    exact (@bmult_one_l B (@bzero B)).
  - change (bpow B (@bzero B) (Datatypes.S (Datatypes.S j)))
      with (@bmult B (bpow B (@bzero B) (Datatypes.S j)) (@bzero B)).
    eapply bae_trans.
    { exact (@bmult_wd B (bpow B (@bzero B) (Datatypes.S j)) (@bzero B)
                        (@bzero B) (@bzero B)
                        IHj (@bae_refl B (@bzero B))). }
    exact (@bmult_zero B (@bzero B)).
Qed.

(* 级数项在零元处塌缩：bzero^{S k}·(1/(S k)!) ≡ bzero *)
Lemma bxdef_esp_term_zero : forall (B : BanachAlg) (k : nat) (q : Q),
  @bae B (@bmult B (bpow B (@bzero B) (Datatypes.S k)) (@bcoef B q))
        (@bzero B).
Proof.
  intros B k q.
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bzero B) (Datatypes.S k)) (@bcoef B q)
                      (@bzero B) (@bcoef B q)
                      (bxdef_bpow_zero_tail B k)
                      (@bae_refl B (@bcoef B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm B q (@bzero B)). }
  exact (@bmult_zero B (@bcoef B q)).
Qed.

(* S3 主加分：exp(0) 级数部分和恒等于 one（bae 等词面） *)
Lemma bxdef_esp_zero_series : forall (B : BanachAlg) (n : nat),
  @bae B (exp_series_partial B (@bzero B) n) (@bone B).
Proof.
  intros B n. induction n as [| m IHm].
  - change (exp_series_partial B (@bzero B) 0%nat) with (@bone B).
    exact (@bae_refl B (@bone B)).
  - change (exp_series_partial B (@bzero B) (Datatypes.S m))
      with (@bplus B (exp_series_partial B (@bzero B) m)
              (@bmult B (bpow B (@bzero B) (Datatypes.S m))
                        (@bcoef B (/ q_fact (Datatypes.S m))))).
    eapply bae_trans.
    { exact (@bplus_wd B (exp_series_partial B (@bzero B) m)
                        (@bmult B (bpow B (@bzero B) (Datatypes.S m))
                                  (@bcoef B (/ q_fact (Datatypes.S m))))
                        (@bone B) (@bzero B)
                        IHm
                        (bxdef_esp_term_zero B m (/ q_fact (Datatypes.S m)))). }
    exact (@bplus_zero B (@bone B)).
Qed.

(* S3 加分范数面：‖exp(0) 的部分和 n‖ == 1（Id 面） *)
Lemma bxdef_esp_zero_bnorm : forall (B : BanachAlg) (n : nat),
  QeqT (@bnorm B (exp_series_partial B (@bzero B) n)) 1%Q.
Proof.
  intros B n.
  pose proof (@bnorm_wd B (exp_series_partial B (@bzero B) n) (@bone B)
             (bxdef_esp_zero_series B n)) as HW.
  pose proof (@bnorm_one B) as H1.
  assert (HQ1 : QeqT (@bnorm B (@bone B)) 1%Q)
    by (destruct H1; apply qeq_imp_qeqT; apply Qeq_refl).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm B (@bone B))).
  - apply qeqT_imp_qeq. exact HW.
  - apply qeqT_imp_qeq. exact HQ1.
Qed.

(* S3 加分极限邻域面：one 与 bxdef_exp bzero 范数任意贴近        *)
(* （exp(0)=bone 的 bae 完全等式面需反可分性字段——              *)
(*   Class 无「范数任意小 ⟹ bae bzero」位，如实遗留不硬攻。）    *)
Lemma bxdef_exp_zero_close : forall (B : BanachAlg) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm B (@bplus B (@bone B)
                           (@bopp B (bxdef_exp B (@bzero B))))) eps.
Proof.
  intros B eps Heps.
  destruct (bxdef_exp_spec B (@bzero B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
  pose proof (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bzero B) N)
                (@bopp B (bxdef_exp B (@bzero B))))
      (@bplus B (@bone B) (@bopp B (bxdef_exp B (@bzero B))))
      (@bplus_wd B (exp_series_partial B (@bzero B) N)
                  (@bopp B (bxdef_exp B (@bzero B)))
                  (@bone B) (@bopp B (bxdef_exp B (@bzero B)))
                  (bxdef_esp_zero_series B N)
                  (@bae_refl B (@bopp B (bxdef_exp B (@bzero B)))))) as HWn.
  exact (QeqT_Qlt_bool_cong _ _ eps HWn HN).
Qed.

(* ============================================================ *)
(* 遗留登记（对称，不落承认件）：                                *)
(*   ① S3 exp_add（交换 e^{a+b}=e^a·e^b）、S4 可逆性：非本席，   *)
(*      依赖闭包承 UpReqBanachExp 文件尾四步登记（本件第②步      *)
(*      「极限定义经 bcauchy_complete_sig」已由本件补齐落位）。   *)
(*   ② exp(0)=bone 完全等式面：需 Class 增反可分性字段           *)
(*      （bnorm 任意小 ⟹ bae bzero）——接口扩容属上游裁决，       *)
(*      本件不擅动 UpReqBanachExp（禁碰在飞件），交邻域面闭合。  *)
(*   ③ 极限唯一性（同序列双极限 bae 相等）：同②依赖反可分性，    *)
(*      非本席可解，如实遗留。                                   *)
(* ============================================================ *)
