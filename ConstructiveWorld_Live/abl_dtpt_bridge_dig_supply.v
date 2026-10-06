(* ==========================================================================)
   abl_dtpt_bridge_dig_supply.v — DTPT 扩容批卷二另半（Bridge_Dig）供给卷
   ── DTPT_Bridge_Dig.v 本体 10 前件槽之卷二另半：普查底册
      §2.4 登记序：本卷 10 槽全做（底册初判全 🟢 纯计算/在库现成路径位）。
      红线遵守：W-DTPTTRUTH-DIAG-01 七槽（diag_closed 形，Truth 域）绝对禁碰
      （本域零此形，零触碰实录）；AT 移交的 Truth 🟡 五槽（Forall2/ev_cong/enum In，
      存疑-②）本卷不做（候二审）；Bridge_Rot 12 槽（X §2.5，卷三 tbr_）本卷不做；
      宿主/桥面禁重计：§S8/§S9 宿主面槽（dtr_ Rotation 版图内）零触碰。
   ① 模块名+使命：abl_dtpt_bridge_dig_supply——逐槽一条供给定理（tdbg_ 前缀），
      陈述形＝「库内既有组合 ⟹ DTPT_Bridge_Dig X 槽前件」：凡宿主在库有同形
      既有件者直供引述（exact 既有件），无者 born-in-place 小步构造（构造子
      反射/等词改写/bool 判定归约），推导只吃已导出内容（Require 库件四件：
      DTPT＋DTPT_DigTheory＋DTPT_Extract＋DTPT_Bridge_Dig；AQ 坑卡① 照办：
      透传 Require 不导出短名，本件自 Require 全链并显式 Import）。
      供给形三类分布：实例域直供（吃宿主既有件）6 条（#1/2/3/6/7/10）＋
      计算律/判定归约 born-in-place 2 条（#4/9）＋等词供给形 2 条（#5/8）。
      【参数位对照总表（10 槽＝底册 §2.4 登记号）】
        槽 1  →tdbg_is_num_size1_set_h1（:54，INV 实例 dQ x，吃 is_num_eq_dQ）
        槽 2  →tdbg_sub_dig_size_mono_set_h1（:77，BOOL 见证，吃 sub_dig_witness）
        槽 3  →tdbg_sub_dig_size_dec_true_h1（:90，同形逐槽一条）
        槽 4  →tdbg_dig_eqb_size_dec_true_h1（:100，BOOL 判定面 born-in-place）
        槽 5  →tdbg_dig_Q_roundtrip_set_h1（:112，EQ 对角等词见证）
        槽 6  →tdbg_gate_pass_QleT_h1（:146，BOOL 金标准实例，吃 u12_gate_pass_t1_h0）
        槽 7  →tdbg_u12_gate_chain_QleT_h1（:160，BOOL 放行实例，
                吃 u12_gate_chain_301_t5）
        槽 8  →tdbg_dig_dec_sound_h1（:200，EQ 等词供给形 x = y ⟹ dQ x = dQ y）
        槽 9  →tdbg_dig_dec_shape_h1（:207，BOOL 对角实例 born-in-place）
        槽 10 →tdbg_dig_dec_size_h1（:215，BOOL 边界见证，吃宿主
                dig_dec_not_eq_witness 前件合取支）
      【应用演示（底册 §4.2 A 直供形使用面）】
        u12_gate_chain_QleT [3;0;1] 5 (tdbg_u12_gate_chain_QleT_h1)
          ⟹ prod (dQleT (H_adj [3;0;1]) 5) (dQleT (H_adj (P0 [3;0;1]))
              (H_adj (Pinf [3;0;1] 0)))——门控全链双门 QleT 证书对落地；
        dig_dec_size (dPair (dQ 0) (dQ 0)) (dPair (dQ 1) (dQ 0))
          (tdbg_dig_dec_size_h1) ⟹ 两码 dig_size 相等（同形同尺寸面）；
        is_num_size1_set (dQ x) (tdbg_is_num_size1_set_h1 x) ⟹ 尺寸 1 见证对
          {n : nat & (n = 1%nat /\ dig_size (dQ x) = n)}；其余各槽同法随应用
          前提落地宿主结论（gate_pass_QleT ⟹ dQleT 0 1；sub_dig_size_dec_true
          ⟹ Nat.leb (dig_size a) (dig_size d) = true 等）。
      【降档口径】供给定理取「槽前件的可满足实例/等词提供形」：宿主槽前件为
        全称变元上的假设（如 sub_dig a d = true／gate_pass t h = true／
        dig_dec a b = true／a = b），无条件泛形多不恒真（如 sub_dig a d = true
        于非子项对落假——宿主 sub_dig_witness_neg :604 反例在档；gate_pass t h
        = true 于 h > t 落假——u12_gate_pass_t1_h2 反例在档），故供给＝给出
        现档可判定的实例域（dQ x／dPair dQ dQ／金标准门对 [3;0;1]×5／
        阈值 1×H 0／对角）或等词供给形，槽语义「前件可由库内既有件提供」
        逐槽成立；宿主结论方向不桥假命题（dig_Q_roundtrip 只取 d = dQ x 向、
        dig_dec 只做可靠下近似——宿主件内 S5 边界声明在案，本件不越界）。
   ② 依赖清单：Stdlib（QArith.QArith/List/Bool/Arith）＋库件 DTPT、
      DTPT_DigTheory、DTPT_Extract、DTPT_Bridge_Dig（统一缓存
      vo_local_world_unified_0930 在册 .vo 只读依赖，零重编零级联；本件
      Require 顺序＝先 stdlib 后库序，禁逆向；dig_dec/dig_tag/dig_dec_not_eq_witness
      在 DTPT_Bridge_Dig.DTPT_Bridge_Dig 模块内，本件第四 Require 显式直取；
      gate_pass/H_adj/P0/Pinf 在 DTPT.DTPT，u12_gate_chain/u12_phase_side_bool/
      u12_gate_pass_t1_h0/u12_gate_chain_301_t5 在 DTPT_Extract.DTPT_Extract，
      is_num_eq_dQ/sub_dig_witness 在 DTPT_DigTheory.DTPT_DigTheory）。
   ③ 对标行：AV 卷二工艺＝abl_dtpt_dig_supply.v（A 直供形/头注五字段/查重
      登记块/绿判四件套/应用演示入头注，同族工艺直接复用）；AT 卷一同族；
设计依据＝普查底册 §2.4（Bridge_Dig 10 槽全
🟢，本卷全做）＋§3（§8 桥面使用链 all_B7 供给需求）／§4（卷2 另半）；
      坑卡预读：AQ（无 Not 大写名——本件零 Not 大写位；`<>` 记法本件零使用；
      grep -c 零命中退码 1 断链——道闸与绿判各步分号独立跑）/AL（语句面零
      Or 形出口）/AS（trans 三实参——本件零 trans 引用）/AO（Q 值序列世界
      甄别：本件 list Q 面与宿主同域，零混载）。
   ④ 构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Set 层载体
      （Q/nat/bool/Dig/list Q 全宿主既有，本件零新增数据载体、零
      Definition/Fixpoint/Inductive）；语句面零混载（零析取/零存在/零经典
      逻辑/零否定出口）；供给对象全为可判定离散前件（bool 判定面/等词），
      可提取性由被引宿主件既有提取锚承载（宿主件 §6 b4_ 提取块＋尾 Print
      Assumptions 面在册，本件零 Obj.magic 面）；nat 层显式 %nat、Q 字面
      一律 %Q（防 Q_scope 劫持）。
   ⑤ 编译配方（池 cwd＝沙箱/现役/abl_tmine04_pool/dtpt_v2b，路径绝对化）：
      source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_bridge_dig_supply.v
      （道闸：起编前 ps -axo comm|grep -ci rocq 独立跑、禁入 && 链；绿判
      四件套：EXIT=0 无管道真取／日志真错行计 0＋逐条 Print Assumptions 全
      Closed／.vo 头 8 字节与宿主 DTPT_Bridge_Dig.vo 同款／.vo 新于 .v；
      第五证 rocq check 分号独立跑。）
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑、零节变量声明位，全部供给定理 Qed 闭合；10 供给定理逐条
      Print Assumptions 全 Closed；DTPT_Bridge_Dig.v 宿主零字节不动（零重编）。
   ========================================================================== *)

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）名面：本件全部顶层名 10 枚全 tdbg_ 新前缀（tdbg_＝Bridge_Dig  *)
(*   批卷二另半专用 prefix），Live 全树＋统一缓存 vo_local_world_unified_  *)
(*   0930 全量 grep 零命中（施工前复检实录）；与已占 dtd_/  *)
(*   dte_/dtr_/dtb_ 四前缀及 AT 卷一 tdt_、AV 卷二 tdg_ 专prefix 零撞     *)
(*   零别名转发；件名 abl_dtpt_bridge_dig_supply.v 全树零命中。           *)
(*   （二）槽面：本卷 10 槽＝底册 §2.4 登记号逐位对表（①总表），坐标      *)
(*   10 位（:54/:77/:90/:100/:112/:146/:160/:200/:207/:215）与底册   *)
(*   现档核验逐位吻合，零漂移；零双供零漏账（10＝Bridge_Dig 域槽总数，    *)
(*   对账平）；同形槽（2↔3、9↔10 均为 sub_dig/dig_dec 前件面）逐位各立    *)
(*   一条（逐槽一条铁律），供给语句同形系槽前件同形所致，非重复计数；      *)
(*   实例域取异（槽 9 对角 dQ 对、槽 10 宿主边界见证 dPair 异值对）以显    *)
(*   各参数位各自供给语义。                                                  *)
(*   （三）宿主界：DTPT_Bridge_Dig.v 本体零字节不动、零重编；两档 diff    *)
(*   逐字同档实测；本件 Require 统一缓存只读在册 .vo，宿主重编  *)
(*   零级联于本件，本件重编零级联于宿主。                                *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_DigTheory.
Require DTPT_Extract.
Require DTPT_Bridge_Dig.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.
Import DTPT_Extract.DTPT_Extract.
Import DTPT_Bridge_Dig.DTPT_Bridge_Dig.

Open Scope Q_scope.

(* ========== 批一：判定器/子项序族五槽（#1-5） ========== *)

(* 槽 1（DTPT_Bridge_Dig.v:54 is_num_size1_set 槽1）：is_num d = true ——
   数值域实例 d := dQ x：宿主既有件 is_num_eq_dQ（DTPT_DigTheory.v:355）直供。
   应用后 is_num_size1_set 给出尺寸 1 见证对（头注①演示）。 *)
Theorem tdbg_is_num_size1_set_h1 : forall x : Q, is_num (dQ x) = true.
Proof.
  exact is_num_eq_dQ.
Qed.

(* 槽 2（:77 sub_dig_size_mono_set 槽1）：sub_dig a d = true —— 真子项见证
   实例：吃宿主定义性见证 sub_dig_witness（DTPT_DigTheory.v:604）直供。
   应用后 sub_dig_size_mono_set 给出 leb 左支或右支 nat 判定见证。 *)
Theorem tdbg_sub_dig_size_mono_set_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 3（:90 sub_dig_size_dec_true 槽1）：sub_dig a d = true —— 同形槽
   逐槽一条（同吃 sub_dig_witness）。应用后 sub_dig_size_dec_true 给出
   Nat.leb (dig_size a) (dig_size d) = true。 *)
Theorem tdbg_sub_dig_size_dec_true_h1 :
  sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q)) = true.
Proof.
  exact sub_dig_witness.
Qed.

(* 槽 4（:100 dig_eqb_size_dec_true 槽1）：dig_eqb a b = true —— bool 判定面
   born-in-place：对角数值对 (dQ 0, dQ 0) 处判定器归约 Qeq_bool 反射落真。
   应用后 dig_eqb_size_dec_true 给出尺寸 leb 真支。 *)
Theorem tdbg_dig_eqb_size_dec_true_h1 : dig_eqb (dQ 0%Q) (dQ 0%Q) = true.
Proof.
  reflexivity.
Qed.

(* 槽 5（:112 dig_Q_roundtrip_set 槽1）：d = dQ x —— 对角等词见证：
   实例域 d := dQ x 处前件反射成立（头注：宿主只取 d = dQ x 向，本件同向
   不越界）。应用后 dig_Q_roundtrip_set 给出 dQeqT (dig_Q (dQ x)) x。 *)
Theorem tdbg_dig_Q_roundtrip_set_h1 : forall x : Q, dQ x = dQ x.
Proof.
  intros x. reflexivity.
Qed.

(* ========== 批二：门控全链族两槽（#6-7） ========== *)

(* 槽 6（:146 gate_pass_QleT 槽1）：gate_pass t h = true —— 金标准门对实例
   （阈值 1、H 0，宿主 §2 样例表首行）：吃宿主行为锚 u12_gate_pass_t1_h0
   （DTPT_Extract.v:45）直供。应用后 gate_pass_QleT 给出 dQleT 0 1 证书。
   反例面：gate_pass 1 2 = false（u12_gate_pass_t1_h2 在档），故实例域
   供给为唯一诚实形。 *)
Theorem tdbg_gate_pass_QleT_h1 : gate_pass 1%Q 0%Q = true.
Proof.
  exact u12_gate_pass_t1_h0.
Qed.

(* 槽 7（:160 u12_gate_chain_QleT 槽1）：u12_gate_chain l t = true —— 双门
   放行实例（乱序列 [3;0;1]、阈值 5，宿主 §3 行为锚）：吃
   u12_gate_chain_301_t5（DTPT_Extract.v:133）直供。应用后
   u12_gate_chain_QleT 给出双门 dQleT 证书对（头注①演示；§8 桥面
   all_B7 使用链之供给需求位，底册 §3 判）。 *)
Theorem tdbg_u12_gate_chain_QleT_h1 : u12_gate_chain [3%Q;0%Q;1%Q] 5%Q = true.
Proof.
  exact u12_gate_chain_301_t5.
Qed.

(* ========== 批三：dig_dec 双判族三槽（#8-10） ========== *)

(* 槽 8（:200 dig_dec_sound 槽1）：a = b —— 等词供给形：Q 值等词 ⟹
   构造子等词（Leibniz 双腿改写）。应用后 dig_dec_sound 给出
   dig_dec (dQ x) (dQ y) = true（可靠性面）。 *)
Theorem tdbg_dig_dec_sound_h1 : forall x y : Q, x = y -> dQ x = dQ y.
Proof.
  intros x y H. rewrite H. reflexivity.
Qed.

(* 槽 9（:207 dig_dec_shape 槽1）：dig_dec a b = true —— 对角数值对实例
   born-in-place（形状＋尺寸双判落真）。应用后 dig_dec_shape 给出
   dig_tag (dQ 0) = dig_tag (dQ 0)。 *)
Theorem tdbg_dig_dec_shape_h1 : dig_dec (dQ 0%Q) (dQ 0%Q) = true.
Proof.
  reflexivity.
Qed.

(* 槽 10（:215 dig_dec_size 槽1）：dig_dec a b = true —— 宿主 §5 边界见证
   实例（dPair (dQ 0)(dQ 0) 与 dPair (dQ 1)(dQ 0) 同形同尺寸而 Leibniz
   不等——完备性反例对）：吃宿主 dig_dec_not_eq_witness（:225）前件合取支
   直供。应用后 dig_dec_size 给出两码 dig_size 相等；此实例并实录
   「dig_dec = true 不保 Leibniz 相等」之宿主 S5 边界语义。 *)
Theorem tdbg_dig_dec_size_h1 :
  dig_dec (dPair (dQ 0%Q) (dQ 0%Q)) (dPair (dQ 1%Q) (dQ 0%Q)) = true.
Proof.
  exact (proj1 dig_dec_not_eq_witness).
Qed.

(* ========== 假设面自查（公理面自审附件，10 供给定理逐条打印） ========== *)
Print Assumptions tdbg_is_num_size1_set_h1.
Print Assumptions tdbg_sub_dig_size_mono_set_h1.
Print Assumptions tdbg_sub_dig_size_dec_true_h1.
Print Assumptions tdbg_dig_eqb_size_dec_true_h1.
Print Assumptions tdbg_dig_Q_roundtrip_set_h1.
Print Assumptions tdbg_gate_pass_QleT_h1.
Print Assumptions tdbg_u12_gate_chain_QleT_h1.
Print Assumptions tdbg_dig_dec_sound_h1.
Print Assumptions tdbg_dig_dec_shape_h1.
Print Assumptions tdbg_dig_dec_size_h1.
