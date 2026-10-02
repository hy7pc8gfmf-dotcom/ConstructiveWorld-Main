(* 五字段指针｜使命：D4-S1「e-π 模量对照·对照主语句＋双侧 witness 换形」——对照
   主语句 lw4c_contrast_face（Set 面并置）＋双侧 witness 换形（lic 形→sigT 嵌套
   Set 面纯机械拆装，零数学新内容）。依赖：S01/S02/S03 基础层与判据面。             
   PiEnvelope、SumInvFactEscape 等。材料源：UpReqIrrationalCriterion        
   (lic_witness_e :723【M】)、LW0MLicBridge (lw0m_e :16/lw0m_xL :20)、LW0LeibWindow
   (:941 认证同形)、PiEnvelope (S2 后续预留)。构造性：零承认式语句；语句面全 Set 层
   （sigT 嵌套＝:941 认证同形；And＝S01 :46 A×B Set 值）；π 侧供件只立名不构造，
   (b) 依赖收拢于 lw4c_pi_lic_face 供件缺位，候 585 β 定理 S5/S6（零伪造）。纪律：
   禁Lra/Reals；提取＋PA 验 Obj.magic=0。编译配方：9.1直调。   *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.        (* Set 层逻辑件：And :46【M】(A×B 面)/NatLe :88【M】 *)
Require Import S02_CauchyComplete.  (* QltT :48【M】/Real/real_metric *)
Require Import S03_QExp.            (* q_fact :43【T】/exp_series :788【T】 *)
Require Import SumInvFactEscape.    (* sif 逃逸机件（lic_witness_e 证明体依赖随件） *)
Require Import LW0LeibWindow.       (* leiblw_Id/Qltb 砖/形态分离族——S2 预留＋备案 B 面 *)
Require Import PiEnvelope.          (* pie_mag 系——S2 后续预留；S1 面零消费名 *)
Require Import LW0MLicBridge.       (* lw0m_e :16/lw0m_xL :20 *)
Require Import UpReqIrrationalCriterion.  (* lic_witness_e :723【M】/lic_escape_window :242【M】 *)

(* ============================================================ *)
(* §1 模量记录（对照对象面）                                      *)
(* ============================================================ *)
(* e 侧窗＝1/n!（阶乘衰减）。逐 token 同 lic_witness_e 第二参 lambda
   （:723-724【M】）——exact 使用零转换缺口（594 细化：581 稿 (1#1) 形
   改 1%Q 形，语义同分、转换风险归零） *)
Definition lw4c_e_win (n : nat) : Q := 1%Q / q_fact n.

(* π 侧窗＝5·pie_mag n＝5/(2n+1)（调和衰减）。lw0m_e 不透明直代 *)
Definition lw4c_pi_win (n : nat) : Q := lw0m_e n.

(* 模量并置记录：A×B 逐字（红线②）；prod 双参 (nat->Q):Set，零 Prop 位 *)
Definition lw4c_modulus_pair : prod (nat -> Q) (nat -> Q) :=
  pair lw4c_e_win lw4c_pi_win.

(* ============================================================ *)
(* §2 e 侧支（lic_witness_e 换形随件）——语句面＝LW0LeibWindow :941
   认证同形：sigT 嵌套＋Prop 守卫位＋Set 值序判定（QltT＝S02 :48【M】） *)
(* ============================================================ *)
Definition lw4c_e_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_e_win n) (Qabs ((q - exp_series n 1)%Q)))).

Lemma lw4c_e_escape_supply : forall q : Q, lw4c_e_escape q.
Proof.
  intro q.
  destruct (lic_witness_e q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* 换形逐 token 对照＝§五.二处方表；exact 若因转换停摆，插入
   `unfold lw4c_e_win.` 于 exact 前一行（预案，禁其他改动）。 *)

(* ============================================================ *)
(* §2' e 侧 lic 形直承面（换形第 0 步：定义性零证直代）
   ——检验①⑤放行前提；如环境拒承：删本段两件、以 §2 面为准，
   备案 B 切换零级联（§2 面不依赖 §2'）                            *)
(* ============================================================ *)
Definition lw4c_e_lic_face : Set :=
  lic_escape_window (fun n => exp_series n 1) lw4c_e_win.
Definition lw4c_e_lic_supply : lw4c_e_lic_face := lic_witness_e.

(* ============================================================ *)
(* §3 π 侧支（LIC 窗形，与 e 侧同构；供件＝(b) 随件，本切片零构造
   ——占位件规格与零伪造护栏＝§六）                                *)
(* ============================================================ *)
Definition lw4c_pi_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)))).

Definition lw4c_pi_lic_face : Set :=
  lic_escape_window lw0m_xL lw4c_pi_win.

Lemma lw4c_pi_escape_of_lic :
  lw4c_pi_lic_face -> forall q : Q, lw4c_pi_escape q.
Proof.
  intro Hlic. intro q.
  destruct (Hlic q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* 纯 destruct 拆装引理：非 (b) 依赖（供件位假设化），本切片可闭合；
   此处源面与目标面 token 逐字同一（lic_escape_window lw0m_xL lw4c_pi_win
   展开体≡lw4c_pi_escape 体），exact 零转换。 *)

(* ============================================================ *)
(* §4 对照主语句＋参数化闭合                                      *)
(* ============================================================ *)
(* And＝S01 :46【M】Set 值 And（A×B 逐字，红线②）；两参各为
   `forall q : Q, …escape q`——Q:Set 上 Set 值全称，落 Set ✓。
   备案 B（检验⑤若判 And 位不可承 Type 级支）：改嵌套 sigT 面
   sigT (fun He : forall q, lw4c_e_escape q => forall q, lw4c_pi_escape q)
   （:941 同构先例零 And），证体改 intro Hlic. exists lw4c_e_escape_supply.
   exact (lw4c_pi_escape_of_lic Hlic). 零级联。 *)
Definition lw4c_contrast_face : Set :=
  And (forall q : Q, lw4c_e_escape q)
      (forall q : Q, lw4c_pi_escape q).

Theorem lw4c_contrast_param : lw4c_pi_lic_face -> lw4c_contrast_face.
Proof.
  intro Hlic. split.
  - exact lw4c_e_escape_supply.
  - exact (lw4c_pi_escape_of_lic Hlic).
Qed.
(* 左支在库直代（lic_witness_e 换形）；右支假设位承载——585 β 定理
   S5/S6 出闸后以闭式供件消去假设位，升格 lw4c_contrast（§6 注记区）。 *)

(* ============================================================ *)
(* §5 对照数值随件（在库承引，不重铸；vm_compute 判例落 S2）        *)
(* ============================================================ *)
Check leiblw_margin_tbl.
Check leiblw_natwin_tbl.

(* ============================================================ *)
(* §6 注记区（S2/(b) 后预留名——本切片零落，禁进编译面）            *)
(*   lw4c_shape_separation   ：S2 形态定理（引件 leiblw_family_separation
     :971、leiblw_nivwin_bounded :962、leiblw_natwin_unbounded :894；
     对照语义限「窗族形态」，581 §四.四/§五全款承引）
   lw4c_pi_lic_supply        ：(b) 供件（585 β 定理出闸随件，闭式 c(a,b)）
   lw4c_contrast             ：无条件升格
     := pair lw4c_e_escape_supply (lw4c_pi_escape_of_lic lw4c_pi_lic_supply)
   lw4c_pi_escape_of_b    ：(b) 定格接口换形引理（待 (b) 闭合出已证结论）   *)
(* ============================================================ *)

(* ============================================================ *)
(* §7 提取＋PA（关面；红线④）                                     *)
(* ============================================================ *)
Separate Extraction lw4c_modulus_pair lw4c_e_win lw4c_pi_win
  lw4c_e_escape lw4c_e_escape_supply lw4c_pi_escape
  lw4c_pi_escape_of_lic lw4c_contrast_face lw4c_contrast_param.
Print Assumptions lw4c_e_escape_supply.
Print Assumptions lw4c_contrast_param.
(* 目标：提取零 Obj.magic；PA 双发均 Closed under the global context。
   π 侧供件不存在（占位），不进提取值域、不进 PA 面。 *)
