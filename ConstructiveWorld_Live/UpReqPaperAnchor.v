(* ========================================================================= *)
(* UpReqPaperAnchor.v —— 论文引用稳定锚点机制件（A1 锚点基建，ANCHOR-A 席）    *)
(*                                                                           *)
(* 使命：九篇论文引用库内坐标 file:line，随每波大规模替换行号大面积漂移        *)
(* （R105-R111 六波实证；本席开工实勘再取证：UpAblMetaWindow.v               *)
(* mtw_window_two_sided 论文7 引 L172-186，现势 L187，+15 漂移当场复现）。    *)
(* 本件把论文引用从「行号」切换到「稳定锚符号」：库内提供具名锚记录，          *)
(* 论文引用锚符号名；锚符号指向的实现位置随波移动而引用不断链。               *)
(*                                                                           *)
(* 机制四条：                                                                *)
(*   ① 权威定位=定理名主键（decl 行首+词边界唯一命中），辅助行号仅快照；       *)
(*      判词类无定理名块用唯一内容短语级主键（本件首例 eps_split）；           *)
(*      件级锚用保留主键 FILE_LEVEL。                                        *)
(*   ② 锚记录六元组：被锚文件、主键、辅助行号快照、基线 md5、自检日、论文域。  *)
(*   ③ 锚层零 Require 独立于被锚层（承 UpReqIndex.v 先例）：锚的建立/刷新     *)
(*      不触碰目标件、不触发任何 vo 缓存失效，维护成本与替换波解耦。          *)
(*   ④ 刷新协议：每波落云后复验门=主键内容级唯一命中+命中行 vs 快照 diff；     *)
(*      漂移则只改快照三字段（行号/md5/自检日），锚符号名永不变 → 论文不断链。 *)
(*                                                                           *)
(* 机检面（四关可过部分）：主键/件名内容校验和（锚主键被改名即编译红——防篡改  *)
(* 面）、md5 字段 32 位良构不变式、自检日齐刷不变式（刷新日必同步翻）、锚清单  *)
(* 计数闭合、按主键解析面（pan_find：论文侧「主键→锚记录」解析在件内机检，    *)
(* 含后缀族混淆机检排除）。                                                  *)
(* 诚实边界：Coq 件内无文件 I/O，「主键在被锚件内唯一命中」不能件内自证，      *)
(* 该半边归复验脚本门（设计单 §四.1）；件内机检面+脚本内容门两层合成完整锚门。 *)
(*                                                                           *)
(* 与 UpReqIndex.v ng_ 登记面关系：ng_=件级在册账（归注册波管辖），pan_=论文   *)
(* 引用坐标账（归论文修订战役管辖）；两面以 pan_file+pan_symbol 弱耦合，      *)
(* 互不依赖；未来 Index 扩列（v4.22+）若增设锚列可由本件导出，本件不动。      *)
(*                                                                           *)
(* 红线自审：零网络；零触碰 order×3/_CoqProject/UpReqIndex.ng_/他席文件；     *)
(* 零公理零承认件全 Qed 纯构造无经典逻辑；自建前缀 pan_（order×3 全表         *)
(* grep=0、Live_X decl 词面 grep=0，开工核验）；坐标/行号/md5 全为            *)
(* 20260922 开工实勘值，非任何任务书字面转录。文尾 Print Assumptions 审计。   *)
(* 归属申报（fail-loud）：pan_paper 为 REIN 清单 A1 批次级归属，带 ? 者为逐篇 *)
(* 精确归属待验（归 A2/A3 格式波复核），本席不冒充实证。                      *)
(* 编译：coqc -q -Q . "" UpReqPaperAnchor.v（9.1 工具链，born-in-place）      *)
(* ========================================================================= *)

From Stdlib Require Import Ascii String.

(* ---------- 锚记录类型 ---------- *)

Record PaperAnchor : Set := MkPaperAnchor
  { pan_file   : string   (* 被锚文件名（.v） *)
  ; pan_symbol : string   (* 主键：定理名 decl 级 / 唯一内容短语级 / FILE_LEVEL *)
  ; pan_line   : nat      (* 辅助行号快照（锚建立日现势，会漂，仅辅助） *)
  ; pan_md5    : string   (* 被锚件基线 md5（锚建立日全文件摘要） *)
  ; pan_day    : nat      (* 自检日期 yyyymmdd *)
  ; pan_paper  : string   (* 引用方论文域（批次级，带 ? 者精确归属待验） *)
  }.

(* ---------- 机检工具面 ---------- *)

Definition pan_b (b : bool) : nat := if b then 1 else 0.

Definition pan_ck (c : ascii) : nat :=
  match c with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7 =>
      pan_b a0 + 2 * pan_b a1 + 4 * pan_b a2 + 8 * pan_b a3
      + 16 * pan_b a4 + 32 * pan_b a5 + 64 * pan_b a6 + 128 * pan_b a7
  end.

Fixpoint pan_sck (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => pan_ck c + pan_sck s'
  end.

Fixpoint pan_slen (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ s' => S (pan_slen s')
  end.

Fixpoint pan_len (l : list PaperAnchor) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (pan_len tl)
  end.

Fixpoint pan_seqb (s t : string) : bool :=
  match s, t with
  | EmptyString, EmptyString => true
  | String c s', String d t' => if ascii_dec c d then pan_seqb s' t' else false
  | _, _ => false
  end.

Fixpoint pan_find (k : string) (l : list PaperAnchor) : option PaperAnchor :=
  match l with
  | nil => None
  | cons a tl => if pan_seqb k (pan_symbol a) then Some a else pan_find k tl
  end.

(* ---------- 首批 8 锚（坐标/md5 = 20260922 开工实勘） ---------- *)

(* 论文1/2 第二定律面：SecondLawQuantified.v 两锚（PR-A/B/C 论文1/2 域） *)
Definition pan_slq_entropy_gain_kl_lower : PaperAnchor :=
  MkPaperAnchor "SecondLawQuantified.v" "slq_entropy_gain_kl_lower" 243
    "f00e7b8fbbe4feba99818bbe7ba841eb" 20260922 "P1/P2".

Definition pan_slq_second_law_eps_list : PaperAnchor :=
  MkPaperAnchor "SecondLawQuantified.v" "slq_second_law_eps_list" 498
    "f00e7b8fbbe4feba99818bbe7ba841eb" 20260922 "P1/P2".

(* 引擎天花板 cec_trunc_sup：REIN A1 首批；精确论文归属待验 *)
Definition pan_cec_trunc_sup : PaperAnchor :=
  MkPaperAnchor "UpReqEngineCeiling.v" "cec_trunc_sup" 275
    "1095c5835c4ef1a563dafbcbb33b75c8" 20260922 "P1/P2?".

(* 论文5 域：UpReqPinskerCore.v ε-三分判词（无定理名块，唯一内容短语级主键；
   现势 L24；精确论文归属待验） *)
Definition pan_pnk_eps_trichotomy : PaperAnchor :=
  MkPaperAnchor "UpReqPinskerCore.v" "eps_split" 24
    "f616d4b7ed858041729198b63d1021b9" 20260922 "P5?".

(* 论文4：SqrtfCauchyArch.v 消融五锚之一（REIN A9 面） *)
Definition pan_sfcy_arch_decay_slot : PaperAnchor :=
  MkPaperAnchor "SqrtfCauchyArch.v" "sfcy_arch_decay_slot" 446
    "d1ffe23723b7f6506e6a047ebfee6172" 20260922 "P4".

(* 论文7：UpAblMetaWindow.v 窗定理——漂移活体（论文引 L172-186，现势 L187） *)
Definition pan_mtw_window_two_sided : PaperAnchor :=
  MkPaperAnchor "UpAblMetaWindow.v" "mtw_window_two_sided" 187
    "ffa0c2662e6d8bc91db45fc6882c3627" 20260922 "P7".

(* 论文7：UpReqUMixSelect.v——PR-D 勘误#2 悬案销案供料（声明行现勘 L532） *)
Definition pan_ums_k_select : PaperAnchor :=
  MkPaperAnchor "UpReqUMixSelect.v" "ums_k_select" 532
    "cbf1aba4caaa77dd68789a55f5316502" 20260922 "P7".

(* 论文6/7：UpReqConcFin2.v 件级锚（FILE_LEVEL 保留主键，现势全件 1644 行） *)
Definition pan_upreq_concfin2_file : PaperAnchor :=
  MkPaperAnchor "UpReqConcFin2.v" "FILE_LEVEL" 1644
    "852d27ee570b086e20b91f6841da339d" 20260922 "P6/P7".

(* ---------- 锚清单（增册=尾部 cons 一节，append-only） ---------- *)

Definition pan_anchor_list : list PaperAnchor :=
  pan_slq_entropy_gain_kl_lower :: pan_slq_second_law_eps_list ::
  pan_cec_trunc_sup :: pan_pnk_eps_trichotomy :: pan_sfcy_arch_decay_slot ::
  pan_mtw_window_two_sided :: pan_ums_k_select :: pan_upreq_concfin2_file :: nil.

(* ---------- 机检不变式面 ---------- *)

(* 主键内容校验和：锚主键被改名/手滑改串即编译红（防篡改面） *)
Lemma pan_sym_ck_invariant :
  pan_sck (pan_symbol pan_slq_entropy_gain_kl_lower) = 2684 /\
  pan_sck (pan_symbol pan_slq_second_law_eps_list) = 2448 /\
  pan_sck (pan_symbol pan_cec_trunc_sup) = 1389 /\
  pan_sck (pan_symbol pan_pnk_eps_trichotomy) = 979 /\
  pan_sck (pan_symbol pan_sfcy_arch_decay_slot) = 2104 /\
  pan_sck (pan_symbol pan_mtw_window_two_sided) = 2160 /\
  pan_sck (pan_symbol pan_ums_k_select) = 1278 /\
  pan_sck (pan_symbol pan_upreq_concfin2_file) = 759.
Proof. repeat split; reflexivity. Qed.

(* 被锚件名内容校验和 *)
Lemma pan_file_ck_invariant :
  pan_sck (pan_file pan_slq_entropy_gain_kl_lower) = 2094 /\
  pan_sck (pan_file pan_slq_second_law_eps_list) = 2094 /\
  pan_sck (pan_file pan_cec_trunc_sup) = 1954 /\
  pan_sck (pan_file pan_pnk_eps_trichotomy) = 1782 /\
  pan_sck (pan_file pan_sfcy_arch_decay_slot) = 1679 /\
  pan_sck (pan_file pan_mtw_window_two_sided) = 1655 /\
  pan_sck (pan_file pan_ums_k_select) = 1652 /\
  pan_sck (pan_file pan_upreq_concfin2_file) = 1379.
Proof. repeat split; reflexivity. Qed.

(* md5 字段 32 位良构不变式 *)
Lemma pan_md5_len_invariant :
  pan_slen (pan_md5 pan_slq_entropy_gain_kl_lower) = 32 /\
  pan_slen (pan_md5 pan_slq_second_law_eps_list) = 32 /\
  pan_slen (pan_md5 pan_cec_trunc_sup) = 32 /\
  pan_slen (pan_md5 pan_pnk_eps_trichotomy) = 32 /\
  pan_slen (pan_md5 pan_sfcy_arch_decay_slot) = 32 /\
  pan_slen (pan_md5 pan_mtw_window_two_sided) = 32 /\
  pan_slen (pan_md5 pan_ums_k_select) = 32 /\
  pan_slen (pan_md5 pan_upreq_concfin2_file) = 32.
Proof. repeat split; reflexivity. Qed.

(* 自检日齐刷不变式：复验刷新必须整列翻新（机械提醒），禁单锚漏刷 *)
Lemma pan_day_uniform_invariant :
  pan_day pan_slq_entropy_gain_kl_lower = 20260922 /\
  pan_day pan_slq_second_law_eps_list = 20260922 /\
  pan_day pan_cec_trunc_sup = 20260922 /\
  pan_day pan_pnk_eps_trichotomy = 20260922 /\
  pan_day pan_sfcy_arch_decay_slot = 20260922 /\
  pan_day pan_mtw_window_two_sided = 20260922 /\
  pan_day pan_ums_k_select = 20260922 /\
  pan_day pan_upreq_concfin2_file = 20260922.
Proof. repeat split; reflexivity. Qed.

(* 锚清单计数闭合 *)
Lemma pan_anchor_list_len : pan_len pan_anchor_list = 8.
Proof. reflexivity. Qed.

(* ---------- 解析面：论文侧「主键 → 锚记录」件内机检 ---------- *)

Lemma pan_find_slq_entropy_gain_kl_lower :
  pan_find "slq_entropy_gain_kl_lower" pan_anchor_list
    = Some pan_slq_entropy_gain_kl_lower.
Proof. reflexivity. Qed.

Lemma pan_find_slq_second_law_eps_list :
  pan_find "slq_second_law_eps_list" pan_anchor_list
    = Some pan_slq_second_law_eps_list.
Proof. reflexivity. Qed.

Lemma pan_find_cec_trunc_sup :
  pan_find "cec_trunc_sup" pan_anchor_list = Some pan_cec_trunc_sup.
Proof. reflexivity. Qed.

Lemma pan_find_pnk_eps_trichotomy :
  pan_find "eps_split" pan_anchor_list = Some pan_pnk_eps_trichotomy.
Proof. reflexivity. Qed.

Lemma pan_find_sfcy_arch_decay_slot :
  pan_find "sfcy_arch_decay_slot" pan_anchor_list = Some pan_sfcy_arch_decay_slot.
Proof. reflexivity. Qed.

Lemma pan_find_mtw_window_two_sided :
  pan_find "mtw_window_two_sided" pan_anchor_list = Some pan_mtw_window_two_sided.
Proof. reflexivity. Qed.

Lemma pan_find_ums_k_select :
  pan_find "ums_k_select" pan_anchor_list = Some pan_ums_k_select.
Proof. reflexivity. Qed.

Lemma pan_find_upreq_concfin2_file :
  pan_find "FILE_LEVEL" pan_anchor_list = Some pan_upreq_concfin2_file.
Proof. reflexivity. Qed.

(* 后缀族混淆机检排除：未注册后缀名解析为空（ums_k_select vs ums_k_select_le
   教训——主键唯一性判据必须带词边界，本面在件内机检该语义） *)
Lemma pan_find_suffix_family_miss :
  pan_find "ums_k_select_le" pan_anchor_list = None.
Proof. reflexivity. Qed.

(* ---------- 假设审计 ---------- *)

Print Assumptions pan_anchor_list.
Print Assumptions pan_find.
Print Assumptions pan_sym_ck_invariant.
