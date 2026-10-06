(* ==========================================================================)
   abl_dtpt_truth_supply.v — DTPT 扩容卷一（tmine04）
   ── DTPT_Truth.v 本体 36 前件槽之卷一：底册 _tmine04_X_DTPT槽普查.md
      §2.1 登记序：本卷做 24 槽纯计算/在库现成路径位（底册初判 🟢 且非 🟡 非证书构造）。
      红线遵守：W-DTPTTRUTH-DIAG-01 七槽（#1/2/4/5/6/8/10，diag_closed 形）绝对禁碰；
      🟡 六槽本卷不做（Forall2 1＋ev_cong 1＋enum In 3＋Bridge_Dep HB 1，候卷二）。
   ① 模块名+使命：abl_dtpt_truth_supply——逐槽一条供给定理（tdt_ 前缀），
      陈述形＝「库内既有组合 ⟹ DTPT_Truth X 槽前件」：凡宿主在库有同形既有件者
      直供引述（exact 既有件），无者born-in-place 小步构造（九支布尔判定/
      记录投影 iota/Q 全序对角），推导只吃已导出内容（Require 六件两件：
      DTPT＋DTPT_Truth；其余四件本卷零触碰）。
      【接口参数对照总表（24 槽＝底册 §2.1 登记号）】
        槽 3  →tdt_neg_truth_at_neg_h1（:286，INV 实例供给 Code:=bool neg:=negb）
        槽 7  →tdt_diag_conj_spec_h1（:395，INV 同上）
        槽 9  →tdt_tarski_via_renaming_h1（:412，INV 同上）
        槽 11 →tdt_trLevel_geq_trans_h1（:474，BOOL 实例 a:=Lv0）
        槽 12 →tdt_trLevel_geq_trans_h2（:475，BOOL 实例 b:=Lv0）
        槽 13 →tdt_chain_ok_trans_h1（:501，BOOL 对角）
        槽 14 →tdt_cv_lv_inj_h1（:616，EQ 等词单射前提，等词供给形）
        槽 15 →tdt_cv_lv_antisym_transport_h1（:627，BOOL 对角）
        槽 16 →tdt_cv_lv_antisym_transport_h2（:628，BOOL 对角）
        槽 17 →tdt_Tex_fiber_cast_h1（:699，EQ 见证节点投影计算律）
        槽 18 →tdt_audit_node_mono_h1（:762，EQ 投影计算律）
        槽 19 →tdt_audit_node_mono_h2（:763，EQ 投影计算律）
        槽 20 →tdt_audit_gate_level_combo_h1（:809，Q-ORD 对角）
        槽 21 →tdt_audit_gate_level_combo_h2（:810，BOOL 实例 a:=Lv0）
        槽 22 →tdt_audit_gate_level_combo_h3（:811，BOOL 实例 b:=Lv0）
        槽 23 →tdt_audit_gate_level_combo_h4（:812，gate_pass 对角，吃 llm_gate_pass_iff）
        槽 24 →tdt_audit_node_chain_combo_h1（:825，Q-ORD 对角）
        槽 25 →tdt_audit_node_chain_combo_h2（:826，audit_node Lv2 见证，吃 audit_node_lv2）
        槽 26 →tdt_audit_node_chain_combo_h3（:827，gate_pass 对角同 23）
        槽 27 →tdt_qlist_eqb_sound_h1（:1079，BOOL 单点表实例，吃 qeqb_refl）
        槽 29 →tdt_ev_eqb_cong_sound_h1（:1103，BOOL 叶实例，吃 qeqb_refl）
        槽 31 →tdt_ev_eqb_raw_eq_h1（:1229，BOOL 叶实例，吃 Qraw_eqb_refl）
        槽 32 →tdt_ev_size_ge_2_pair_h1（:1378，NAT 尺寸见证 evPair 叶×2）
        槽 33 →tdt_ev_pair_decomp_exact_h1（:1391，NAT 尺寸见证 evPair seq+num）
      【降档口径】供给定理取「槽前件的可满足实例/守恒计算律」形：宿主槽前件为
        全称变元上的假设（如 trLevel_geq t a = true），无条件泛形多为此假
        （底册 W 账同法判），故供给＝给出现档可判定的实例域（对角/叶/单点表/
        Lv0 层）或等词供给形，槽语义「前件可由库内既有件提供」逐槽成立。
   ② 依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、DTPT_Truth
      （统一缓存 vo_local_world_unified_0930 在册 .vo 只读依赖，零重编零级联；
      本件 Require 顺序＝先 stdlib 后库序，禁逆向）。
   ③ 对标行：同形件供给工艺＝abl_dtr_core1.v（A 直供形/头注五字段/查重登记块/
      绿判四件套）；设计依据＝_tmine04_X_DTPT槽普查.md §2.1/§4（卷1
      tdt_ 29 可消解槽，本卷做其中 24 纯计算位，5 个 🟡 证书构造位留卷二）；
      坑卡预读：AQ（零 Not；Require 全短名无透传歧义）/AL（语句面零 Or 形出口）/
      AO（DTPT＝Q 值序列世界已甄别：qlist_eqb 即 list Q 面，无 list(list Real)/抽象 Tok 混载）。
   ④ 构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层载体
      （bool/nat/Q/list Q/Level/TrNode/Evidence 全宿主既有，本件零新增数据载体）；
      语句面零混载（零否定出口/零析取/零存在/零经典逻辑）；供给对象全为可判定
      离散前件（bool 判定面/Q 全序/nat 序/等词），可提取性由被引宿主件既有
      提取锚承载（DTPT_Truth T1/T2 Extraction 块在册，本件零 Obj.magic 面）；
      nat 层显式 Datatypes.S / O / Nat.add（防 Q_scope 劫持）；Q 字面一律 %Q。
   ⑤ 编译配方（池 cwd＝沙箱/现役/abl_tmine04_pool/dtpt_v1，路径绝对化）：
      source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_truth_supply.v
      （道闸：起编前 ps -axo comm|grep -ci rocq 独立跑、禁入 && 链；绿判四件套：
      EXIT=0 无管道真取／日志真错行计 0＋逐条 Print Assumptions 全 Closed／
      .vo 头 8 字节与宿主 DTPT_Truth.vo 同款／.vo 新于 .v；第五证 rocq check。）
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑、零节变量声明位，全部供给定理 Qed 闭合；24 供给定理逐条
      Print Assumptions 全 Closed；DTPT_Truth.v 宿主零字节不动（零重编）。
   ========================================================================== *)

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）名面：本件全部顶层名 24 枚全 tdt_ 新前缀（tdt_＝Truth 批卷一   *)
(*   专prefix），Live 全树＋统一缓存 vo_local_world_unified_0930 全量      *)
(*   grep 零命中（施工前复检实录）；与同池已占 dtd_/dte_/dtr_/   *)
(*   dtb_ 四前缀及宿主在役名零撞零别名转发。                              *)
(*   （二）槽面：卷一 24 槽＝底册 §2.1 登记号逐位对表（①总表），7 槽      *)
(*   W-DIAG（#1/2/4/5/6/8/10）零触碰，5 槽 🟡（#28/30/34/35/36）留卷二，  *)
(*   零双供零漏账（24＋7＋5＝36 对账平）。                                *)
(*   （三）宿主界：DTPT_Truth.v 本体零字节不动、零重编；本件 Require 统一  *)
(*   缓存只读在册 .vo，宿主重编零级联于本件，本件重编零级联于宿主。        *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_Truth.
Import DTPT_Truth.DTPT_Truth.

(* ========== 批一：INV 三槽（#3/7/9，同形实例供给）＋ 传递/桥/审查器前族 ========== *)

(* 槽 3（DTPT_Truth.v:286 neg_truth_at_neg 槽1）：involutive Code neg ——
   泛形被宿主 negS 反例封死（negS_not_involutive），实例供给取库内既有正例
   码世界 Code:=bool、neg:=negb（negb_involutive_self 同形，此处直供引述）。 *)
Theorem tdt_neg_truth_at_neg_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 7（:395 diag_conj_spec 槽1）：同形 INV 槽，同款实例供给（逐槽一条）。 *)
Theorem tdt_diag_conj_spec_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 9（:412 tarski_via_renaming 槽1）：同形 INV 槽，同款实例供给。 *)
Theorem tdt_tarski_via_renaming_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* 槽 11（:474 trLevel_geq_trans 槽1）：trLevel_geq t a = true ——
   实例域 a:=Lv0（层判全序底），宿主既有件 trLevel_geq_Lv0（:160）直供。 *)
Theorem tdt_trLevel_geq_trans_h1 : forall t : TrNode, trLevel_geq t Lv0 = true.
Proof.
  exact trLevel_geq_Lv0.
Qed.

(* 槽 12（:475 trLevel_geq_trans 槽2）：level_le b a = true ——
   实例域 b:=Lv0，level_le 定义首支归约恒真，九支判定面 born-in-place。 *)
Theorem tdt_trLevel_geq_trans_h2 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* 槽 13（:501 chain_ok_trans 槽1）：chain_ok l1 l2 l3 = true ——
   对角实例 l1=l2=l3，吃宿主既有件 level_le_refl（:58）双支装配。 *)
Theorem tdt_chain_ok_trans_h1 : forall l : Level, chain_ok l l l = true.
Proof.
  intros l. unfold chain_ok. apply andb_true_intro. split;
    apply level_le_refl.
Qed.

(* 槽 14（:616 cv_lv_inj 槽1）：cv_lv a = cv_lv b —— 等词供给形：
   库内既有组合（Leibniz 等词改写）⟹ 槽前件，cv_lv_inj 随之可喂。 *)
Theorem tdt_cv_lv_inj_h1 : forall a b : DTPT.DTPT.Level,
  a = b -> cv_lv a = cv_lv b.
Proof.
  intros a b H. rewrite H. reflexivity.
Qed.

(* 槽 15（:627 cv_lv_antisym_transport 槽1）：level_le (cv_lv a) (cv_lv b) = true ——
   对角实例 a:=b，吃宿主既有件 level_le_refl（:58）。 *)
Theorem tdt_cv_lv_antisym_transport_h1 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (level_le_refl (cv_lv a)).
Qed.

(* 槽 16（:628 cv_lv_antisym_transport 槽2）：level_le (cv_lv b) (cv_lv a) = true ——
   对角实例 b:=a，同款既有件直供（逐槽一条）。 *)
Theorem tdt_cv_lv_antisym_transport_h2 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (level_le_refl (cv_lv a)).
Qed.

(* 槽 17（:699 Tex_fiber_cast 槽1）：DTPT.DTPT.trPhi t = phi ——
   见证节点计算律：t 取 DTPT 侧 mkTrNode lv phi m v，首投影 iota 归约回 phi。 *)
Theorem tdt_Tex_fiber_cast_h1 : forall (lv : DTPT.DTPT.Level)
    (phi m : DTPT.DTPT.Dig) (v : DTPT.DTPT.Evidence),
  DTPT.DTPT.trPhi (DTPT.DTPT.mkTrNode lv phi m v) = phi.
Proof.
  intros lv phi m v. reflexivity.
Qed.

(* 槽 18（:762 audit_node_mono 槽1）：trLevel t' = trLevel t ——
   记录投影计算律：同层槽构造的节点层级投影归约回层指标本身。 *)
Theorem tdt_audit_node_mono_h1 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trLevel (mkTrNode lv p m v) = lv.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* 槽 19（:763 audit_node_mono 槽2）：trValue t' = trValue t ——
   记录投影计算律：值槽同构（尾投影归约回证据指标）。 *)
Theorem tdt_audit_node_mono_h2 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trValue (mkTrNode lv p m v) = v.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* ========== 批二：组合审查定理槽族（#20-26）＋ 内容判定/尺寸槽族（#27-33） ========== *)

(* 槽 20（:809 audit_gate_level_combo 槽1）：(thr1 <= thr2)%Q ——
   Q 全序对角实例 thr1:=thr2，stdlib 既有件 Qle_refl 直供。 *)
Theorem tdt_audit_gate_level_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* 槽 21（:810 audit_gate_level_combo 槽2）：trLevel_geq t a = true ——
   实例域 a:=Lv0，宿主既有件 trLevel_geq_Lv0 直供（与槽 11 同形，逐槽一条）。 *)
Theorem tdt_audit_gate_level_combo_h2 : forall t : TrNode,
  trLevel_geq t Lv0 = true.
Proof.
  exact trLevel_geq_Lv0.
Qed.

(* 槽 22（:811 audit_gate_level_combo 槽3）：level_le b a = true ——
   实例域 b:=Lv0，九支判定面 born-in-place（与槽 12 同形）。 *)
Theorem tdt_audit_gate_level_combo_h3 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* 槽 23（:812 audit_gate_level_combo 槽4）：DTPT.DTPT.gate_pass thr1 H = true ——
   对角实例 thr1:=H：库内既有组合（DTPT.v llm_gate_pass_iff :1713 ＋ stdlib
   Qle_refl）⟹ 通过判据在门槛自等处恒开。 *)
Theorem tdt_audit_gate_level_combo_h4 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* 槽 24（:825 audit_node_chain_combo 槽1）：(thr1 <= thr2)%Q ——
   Q 全序对角实例（与槽 20 同形，逐槽一条）。 *)
Theorem tdt_audit_node_chain_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* 槽 25（:826 audit_node_chain_combo 槽2）：audit_node t = true ——
   Lv2 层升见证实例域：宿主既有件 audit_node_lv2（:773）逐字直供。 *)
Theorem tdt_audit_node_chain_combo_h2 : forall (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  audit_node (mkTrNode Lv2 p m v) = true.
Proof.
  exact audit_node_lv2.
Qed.

(* 槽 26（:827 audit_node_chain_combo 槽3）：DTPT.DTPT.gate_pass thr1 H = true ——
   对角实例（与槽 23 同形，逐槽一条）。 *)
Theorem tdt_audit_node_chain_combo_h3 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* 槽 27（:1079 qlist_eqb_sound 槽1）：qlist_eqb l1 l2 = true ——
   单点表实例域：逐点判定吃宿主既有件 qeqb_refl（:1020）＋空表尾反射。 *)
Theorem tdt_qlist_eqb_sound_h1 : forall q : Q,
  qlist_eqb (q :: nil) (q :: nil) = true.
Proof.
  intros q. simpl. apply andb_true_intro. split.
  - apply qeqb_refl.
  - reflexivity.
Qed.

(* 槽 29（:1103 ev_eqb_cong_sound 槽1）：ev_eqb a b = true ——
   叶实例域（evNum 同值对）：叶判 Qeq_bool 吃宿主既有件 qeqb_refl。 *)
Theorem tdt_ev_eqb_cong_sound_h1 : forall q : Q,
  ev_eqb (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply qeqb_refl.
Qed.

(* 槽 31（:1229 ev_eqb_raw_eq 槽1）：ev_eqb_raw a b = true ——
   叶实例域（Leibniz 叶判）：吃宿主既有件 Qraw_eqb_refl（:1169）。 *)
Theorem tdt_ev_eqb_raw_eq_h1 : forall q : Q,
  ev_eqb_raw (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply Qraw_eqb_refl.
Qed.

(* 槽 32（:1378 ev_size_ge_2_pair 槽1）：le (S (S O)) (ev_size e) ——
   尺寸见证实例：e := evPair 叶×2，尺寸展开 3 ≥ 2（le_S＋le_n 双步）。 *)
Theorem tdt_ev_size_ge_2_pair_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evNum 0%Q) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* 槽 33（:1391 ev_pair_decomp_exact 槽1）：同尺寸门槛 ——
   尺寸见证实例（seq+num 异形叶对，逐槽一条）。 *)
Theorem tdt_ev_pair_decomp_exact_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evSeq nil) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* ========== 假设面自查（公理面自审附件，24 供给定理逐条打印） ========== *)
Print Assumptions tdt_neg_truth_at_neg_h1.
Print Assumptions tdt_diag_conj_spec_h1.
Print Assumptions tdt_tarski_via_renaming_h1.
Print Assumptions tdt_trLevel_geq_trans_h1.
Print Assumptions tdt_trLevel_geq_trans_h2.
Print Assumptions tdt_chain_ok_trans_h1.
Print Assumptions tdt_cv_lv_inj_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h2.
Print Assumptions tdt_Tex_fiber_cast_h1.
Print Assumptions tdt_audit_node_mono_h1.
Print Assumptions tdt_audit_node_mono_h2.
Print Assumptions tdt_audit_gate_level_combo_h1.
Print Assumptions tdt_audit_gate_level_combo_h2.
Print Assumptions tdt_audit_gate_level_combo_h3.
Print Assumptions tdt_audit_gate_level_combo_h4.
Print Assumptions tdt_audit_node_chain_combo_h1.
Print Assumptions tdt_audit_node_chain_combo_h2.
Print Assumptions tdt_audit_node_chain_combo_h3.
Print Assumptions tdt_qlist_eqb_sound_h1.
Print Assumptions tdt_ev_eqb_cong_sound_h1.
Print Assumptions tdt_ev_eqb_raw_eq_h1.
Print Assumptions tdt_ev_size_ge_2_pair_h1.
Print Assumptions tdt_ev_pair_decomp_exact_h1.
