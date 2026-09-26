(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   pls_vocab_ne_shim（原 L65，2 句玩具证）                              *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T343 恒等守恒更正注记】2026-09-22 包AW十七 台账席（恒等头注收尾·AD 余六件闭合） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 参数位＋恒等守恒 1 参数位；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339／T341／T343 台账。 *)
(* 附记：T277 判级全文恒等；AD 域余六件收尾收官（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* UpReqPropLiftShim.v — AA13·B6 升面兼容性升级适配引理件（pls_ 前缀）
   ==================================================================
   定性（主会话纠正令 20260914）：本件是「升面兼容性升级」接口件——
   为老基座（S 系拆分层）历史语句形态（祖父条款存量，非红线违规、
   非假设消债）提供「老否定形 ⟷ sigT 见证形」的单向适配引理族，
   让新 Set 层代码免下行依存历史否定形、可直接产/消见证形。
   基座件（S 系/219 壳/G 系）一行未动：本件为纯新增独立件。

   设计（AA8 B6 工单）：
   - pls_vocab_ne       ：目标 Set 层见证形 {l : Tok | InT l vocab}
   - pls_vocab_ne_shim  ：见证形 ⟹ 老形 Not (Id vocab nil)
                          （升面生产者供证，旧依存者语句原样不变）
   - pls_vocab_ne_lift  ：老形 ⟹ 见证形（列表构造子分裂，构造性；
                          AA8「单向 Not→sigT 需列表可判定性」的阻隔位精化：
                          Not (Id vocab nil) 形对具体列表数据免判定性
                          即可分裂——真墙在双重否定/抽象载体形，见交付报告障碍账）
   - pls_Qlt_to_QltT    ：stdlib Qlt(Prop) ⟹ S02 QltT(Set)（缺向补齐；
                          S02 已有反向 QltT_to_Qlt 与 Qle_to_QleT'/QleT'_to_Qle）
   - pls_real_lt_eps/_rest / pls_real_le_cases：real_lt(sigT 见证形,
                          S02:456)/real_le(Or 形) 的依存面投影 accessor

   公理面：本件通过七项禁词扫描（承认类/经典类字面量零命中，
   逐项记录见 E-STAGING-AA13 卡），
   全件 Print Assumptions 预期 Closed（G3 验收）。
   上游：S01_BaseRing（Id/Not/InT 连接词）、S02_CauchyComplete
   （QltT/QleT'/real_lt/real_le/Real）。零新增 Require 面。 *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import List QArith.QArith.
Import ListNotations.

(* ============================================================ *)
(* 1. 目标 Set 层见证形 + 构造/投影 accessor                    *)
(* ============================================================ *)
Definition pls_vocab_ne {Tok : Set} (vocab : list Tok) : Set :=
  sigT (fun l : Tok => InT l vocab).

Definition pls_vocab_ne_intro {Tok : Set} {vocab : list Tok} (l : Tok)
  : InT l vocab -> pls_vocab_ne vocab
  := fun H => existT _ l H.

Definition pls_vocab_ne_witness {Tok : Set} {vocab : list Tok}
  (H : pls_vocab_ne vocab) : Tok
  := projT1 H.

Definition pls_vocab_ne_member {Tok : Set} {vocab : list Tok}
  (H : pls_vocab_ne vocab) : InT (projT1 H) vocab
  := projT2 H.

(* ============================================================ *)
(* 2. 单向适配引理核心：见证形 ⟹ 老依存形（旧依存者兼容面）        *)
(* ============================================================ *)
Lemma pls_inT_nil_empty : forall (A : Set) (x : A), InT x nil -> Empty_set.
Proof.
  intros A x H. inversion H.
Qed.

(* Id 的 J 消解（S01 Id 是 Martin-Löf 恒等型；此形走索引变量退化，免 subst 坑） *)
Lemma pls_id_transport {A : Set} {x y : A} (P : A -> Set)
  (Hxx : P x) (Hxy : Id x y) : P y.
Proof.
  revert Hxx. destruct Hxy. intros Hxx. exact Hxx.
Qed.

Lemma pls_vocab_ne_shim {Tok : Set} (vocab : list Tok)
  (H : pls_vocab_ne vocab) : Not (Id vocab nil).
Proof.
  intros Hnil.
  exact (pls_inT_nil_empty Tok (projT1 H)           (pls_id_transport (fun vv => InT (projT1 H) vv) (projT2 H) Hnil)).
Defined.

(* ============================================================ *)
(* 3. 反向升面：老形 ⟹ 见证形（列表分裂构造性；阻隔位精化实证）  *)
(* ============================================================ *)
Lemma pls_vocab_ne_lift {Tok : Set} (vocab : list Tok) :
  Not (Id vocab nil) -> pls_vocab_ne vocab.
Proof.
  intros Hne. destruct vocab as [|v l'].
  - destruct (Hne id_refl).
  - exact (existT _ v (InT_here v l')).
Defined.

(* 双向复合不丢信息（成员面）：lift∘shim 的复合见证是合法成员。
   （见证精确形可漂移：lift 归一头元，H 见证可取任意成员位——故
   只记成员合法性，不记 Leibniz 见证恒等。） *)
Lemma pls_vocab_ne_shim_lift {Tok : Set} (vocab : list Tok)
  (H : pls_vocab_ne vocab)
  : InT (projT1 (pls_vocab_ne_lift vocab (pls_vocab_ne_shim vocab H))) vocab.
Proof.
  destruct vocab as [|v l'].
  - destruct H as [l Hin]. inversion Hin.
  - simpl. exact (InT_here v l').
Qed.

(* ============================================================ *)
(* 4. Q 层桥薄别名（基座 S02 已备双向：QltT_to_Qlt L29 /        *)
(*    Qlt_to_QltT L38 / Qle_to_QleT' L97 / QleT'_to_Qle L84；   *)
(*    本件只做族内统一命名转发，零重复证明）                    *)
(* ============================================================ *)
Definition pls_Qlt_to_QltT (x y : Q) (H : Qlt x y) : QltT x y
  := Qlt_to_QltT x y H.

Definition pls_Qle_to_QleT' (x y : Q) (H : Qle x y) : QleT' x y
  := Qle_to_QleT' x y H.

Definition pls_QltT_to_Qlt (x y : Q) (H : QltT x y) : Qlt x y
  := QltT_to_Qlt x y H.

Definition pls_QleT'_to_Qle (x y : Q) (H : QleT' x y) : Qle x y
  := QleT'_to_Qle x y H.

(* ============================================================ *)
(* 5. Real 层依存面 accessor（real_lt 本系 sigT 见证形 S02:456） *)
(* ============================================================ *)
Definition pls_real_lt_eps {x y : Real} (H : real_lt x y) : Q := projT1 H.
Definition pls_real_lt_rest {x y : Real} (H : real_lt x y) := projT2 H.
Definition pls_real_le_cases {x y : Real} (H : real_le x y)
  := H : Or (real_lt x y) (real_eq x y).

Print Assumptions pls_vocab_ne_shim.
