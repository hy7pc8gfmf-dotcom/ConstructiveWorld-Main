(* ==========================================================================)
   abl9b_int_prep_57.v — 集成预备件（桥移除迁移与 S11 参数位装配三块）
   ── 数学使命：──────────────────────────────────────────────────────────────
   三块集成面预备，全部不依赖后续层产出：
   块一（件52 桥移除迁移）：旧 raw-w 证书随行桥（abl9b_diff_bridge）移除后
     的等价新引理组——①旧桥→直接使用的 real_eq 运输件（旧桥数学核心的独立保全
     形：raw-w arctan 点与 clamp 代表元 arctan 点的尾域 real_eq）；②Hdiff 位
     直接匹配件（迁移后调用点形：主公式 A2 形直接匹配骨架参数位，无桥无假设束）；③
     迁移后主装配（件52 主定理的移除后等形：直接使用骨架 abl9b，raw-w 证书随行
     假设束整体卸除，结论=目标语句原文逐字）。
   块二（装配链 clamp 化对齐引理组）：件20 abl9_w_align/abl9_arctan_wd_real
     端点对齐改用 clamp 代表元——实层 w↔clamp 尾域运输、除法形端点→clamp
     对齐、arctan 层除法形端点→clamp 对齐（全域逐点等改用尾域逐点等）、
     arctan 层 3/4 半径变体（件53 供给）、clamp↔clamp34 衔接引理。
   块三（S11 参数位装配骨架）：S11 B5A_Item1B 参数位 real_arctan_deriv（出节泛化
     形）的 inhabitation 记录装配——A2 形主公式语句面契约为唯一显式前件参数
     （主公式件进行中，闭合后代入），双字段记录装配包（进行中供给字段+参数位逐字
     闭形字段），另配两个出节使用件（b5n_vdh_pts/b5a_sin_atan_diff）的实参化
     闭形定义与签名符合性见证引理。
   ── 依赖清单：──────────────────────────────────────────────────────────────
   S01–S11（基础模块）；件20 abl_arctan_diff_20（abl9_w_align 除法形对齐、
   abl9_arctan_wd_real 全域逐点合同、abl9_QltT_transfer_l/abl9_Qabs_wd）；
   件45 abl_arctan_diff_45（abl9_arctan_arg_wd 终近逐点合同）；件30
   abl9b_skeleton_30（abl9b 主骨架、abl9b_dom_pos/abl9b_w/abl9b_w_bounds
   尾形/abl9b_wc/abl9b_w_clamp_dom/abl9b_wc_id_pt）；件53 abl9b_rho_chain_53
   （abl9b_wc34/abl9b_w_clamp34_dom/abl9b_wc34_id_pt/abl9b_wc34_w_real_eq）。
   不引件52：桥移除原则——本件为新形态承载件，不回接旧桥；S11 零字节编辑
   （仅 Require 引用，不改动）。不依赖主公式闭合件与后续层件（进行中，以语句面契约为参）。
   ── 对标行：────────────────────────────────────────────────────────────────
   迁移形依据：件52 调用点（abl9b_main_assembly_52.v L156-159 带）改直接
   引用 clamp 代表元；裁决依据：结论右端换 clamp 代表元而定义域逐字
   不动。语句面基准：件30 Hdiff 参数位（abl9b_skeleton_30.v L338-343
   带，与件52 桥结论 L96-99 带逐字一致）；S11 参数位语句：S11_TP3B5.v
   L11855-11867 带（出节泛化后首参即参数位本身）；出节使用件：S11
   L12263-12274 带（b5n_vdh_pts）、L12531-12541 带（b5a_sin_atan_diff）。
   尾域运输先例：件53 abl9b_wc34_w_real_eq（L402 带）；桥运输先例：件52
   桥证明体（L112-121 带）。证明项同一性铁律：件30 L391-392 带（参数位
   w 证书位逐字写 abl9b_dom_pos x h Hx Hh4，
   禁换可转换等价证明项）。
   ── 构造性注记：────────────────────────────────────────────────────────────
   全件真构造闭合，零承认式声明、零悬置前提、零经典逻辑；零承认链短路策略
   （实层链走 real_eq_trans/sym/real_mult_comm 逐环复合，Q 序链走
   QleT'_to_Qle/Qle_trans 系逐链构造）。语句面承载位全 Set/Type 形（real_eq/
   real_lt/real_le/sigT/And 均本库 Set 层形，Qle/Qlt 仅标量前提位）。
   诚实申明三则：①块一②③为直接匹配/重述级承载（移除迁移的语句面形态本身），
   数学重量在①运输件，先例=件16 件1 薄实例化申明；②块二各对齐件前件中的
   raw-w 全域证书与终近域界系链内持证点位使用形（装配期辅助实参），不入主
   公式语句面（逐点界入语句面即量化子供不出，本组引以为戒）；
   ③参数位 w 证书位逐字写 abl9b_dom_pos x h Hx Hh4（real_inv_pos 定义对证明项
   做匹配，假设位不可转换，件30 铁律）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && unset COQLIB ROCQLIB
   cd abl_a2b3_WASH_pool && ulimit -s 65532
   nice -19 rocq c -native-compiler no -Q "$PWD" "" "$PWD/abl9b_int_prep_57.v"
   （单道顺序，发起前进程计数合规；绿判四要素：EXIT=0 真取／真错行计 0／
   主定理 Closed／vo 头 8 字节 436f712100015ff4 且 vo 新于 v。）
   ── 交付声明 ──────────────────────────────────────────────────────────────
   本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、零参数占位、
   零猜想、零中止，全部结论 Qed 真构造闭合；主定理承认面全 Closed，提取
   检验判据 Obj.magic 计 0。池内既有件零字节改动（本件为根目录新件）。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import abl_arctan_diff_20.
Require Import abl_arctan_diff_45.
Require Import abl9b_skeleton_30.
Require Import abl9b_rho_chain_53.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith Extraction.

(* ============================================================ *)
(* 块一 · 件52 桥移除迁移件组                                        *)
(* ============================================================ *)

(* —— ①旧桥→直接使用的 real_eq 运输件（旧桥数学核心的独立保全形）。    *)
(*   数学核：|w_n| ≤ (4/3)|h_n| ≤ 1/3（n≥Nw，abl9b_w_bounds 尾域）⟹      *)
(*   clamp 于尾域逐点恒等（abl9b_wc_id_pt）⟹ arctan 终近逐点合同         *)
(*   （abl9_arctan_arg_wd 件45）⟹ real_eq。                              *)
(*   注：Hw（raw 形全域证书）系链内持证点位使用前件（装配期辅助实参形，诚实 *)
(*   承载）；主公式 A2 形闭合后其结论即本件结论，无须再经本件——本件     *)
(*   为旧桥移除后的内容保全与迁移等价性凭证。Hd 取独立参数形（对任意    *)
(*   正性证明项参数化；参数位面实例一律取 abl9b_dom_pos x h Hx Hh4 逐字）。 *)
Lemma abl9b_int_retire_transport_57 :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
    (Hw : forall n : nat,
           QleT' (Qabs (projT1 (abl9b_w x h Hd) n)) 1),
  real_eq (cauchy_real_arctan (abl9b_w x h Hd) Hw)
          (cauchy_real_arctan (abl9b_wc x h Hd)
             (abl9b_w_clamp_dom (abl9b_w x h Hd))).
Proof.
  intros x Hx h Hh4 Hd Hw.
  destruct (abl9b_w_bounds x h Hx Hh4 Hd) as [Nw HNw].
  apply (abl9_arctan_arg_wd (abl9b_w x h Hd)
           (abl9b_wc x h Hd) Hw
           (abl9b_w_clamp_dom (abl9b_w x h Hd)) Nw).
  intros n Hn.
  apply Qeq_sym.
  apply (abl9b_wc_id_pt (abl9b_w x h Hd) n).
  destruct (HNw n (NatLe_lift _ _ Hn)) as [_ Hw13].
  exact (QleT'_to_Qle _ _ Hw13).
Qed.

(* —— ②Hdiff 位直接匹配件（迁移后调用点形）。                          *)
(*   件52 旧调用点（abl9b_main_assembly_52.v L156-159 带）的迁移等形：   *)
(*   旧形 fun h Hh4 Hxh => abl9b_diff_bridge x Hx h Hh4 Hxh             *)
(*        (Hdiff_raw h Hh4 Hxh) 整体移除，改为 A2 形主公式直接匹配。     *)
(*   A2 形主公式以前件参数承载（语句面=件30 Hdiff 参数位逐字，主公式件闭合 *)
(*   后代入实参即得全量）。薄直接匹配承载，诚实申明见头注构造性注记①。  *)
Lemma abl9b_int_hdiff_direct_57 :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  (* A2 形主公式接口参数（域逐字+clamp 代表元 RHS；w 证书位铁律逐字） *)
  (forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
     (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
   real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
              (real_opp (cauchy_real_arctan x Hx)))
           (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
              (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4))))) ->
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).
Proof.
  intros x Hx Ha2 h Hh4 Hxh.
  exact (Ha2 h Hh4 Hxh).
Qed.

(* —— ③迁移后主装配（件52 主定理的移除后等形）。                        *)
(*   raw-w 证书随行假设束整体卸除（sigT 随行形消解），第 4 步差公式位    *)
(*   以 A2 形主公式直接匹配骨架 abl9b（其内含第 1-3 步 δ 配方/9a-甲 引入与 *)
(*   第 5 步逐点余项+margin 闭合全链），无桥；结论=目标语句原文逐字      *)
(*   （S11 参数位出节目标逐字）。                                        *)
Lemma abl9b_int_assembly_direct_57 :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  (* A2 形主公式接口参数（=件30 Hdiff 参数位语句逐字）  *)
  (forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
     (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
   real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
              (real_opp (cauchy_real_arctan x Hx)))
           (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
              (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4))))) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                        (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hx Ha2 eps Heps.
  exact (abl9b x Hx Ha2 eps Heps).
Qed.

(* ============================================================ *)
(* 块二 · 装配链 clamp 化对齐引理组                                  *)
(*   件20 端点对齐两件改用 clamp 代表元；前件中的 raw 全域证书与终近  *)
(*   域界系链内持证点位使用形（装配期辅助实参），不入主公式语句面（诚实申明 *)
(*   见头注构造性注记②）。                                            *)
(* ============================================================ *)

(* —— 对齐一（实层）：w 与半径 1 clamp 代表元尾域 real_eq。             *)
(*   证法=件53 abl9b_wc34_w_real_eq 的半径 1 同构形：w_bounds 尾形      *)
(*   （|w_n|≤1/3 于 n≥Nw）+wc_id_pt 点位恒等+实层尾域语义提升。         *)
Lemma abl9b_int_w_clamp_real_eq_57 :
  forall (x h : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (abl9b_w x h Hd) (abl9b_wc x h Hd).
Proof.
  intros x h Hx Hh4 Hd e He.
  destruct (abl9b_w_bounds x h Hx Hh4 Hd) as [Nw HNw].
  exists Nw. intros n Hn.
  destruct (HNw n Hn) as [_ Hb13].
  assert (Hid : projT1 (abl9b_wc x h Hd) n == projT1 (abl9b_w x h Hd) n)
    by (apply (abl9b_wc_id_pt (abl9b_w x h Hd) n);
        exact (QleT'_to_Qle _ _ Hb13)).
  apply abl9_QltT_transfer_l with (x := 0%Q)
    (y := Qabs (projT1 (abl9b_w x h Hd) n - projT1 (abl9b_wc x h Hd) n)).
  - assert (Hz : projT1 (abl9b_w x h Hd) n - projT1 (abl9b_wc x h Hd) n
                 == 0%Q)
      by (rewrite Hid; ring).
    apply Qeq_sym.
    apply (Qeq_trans _ (Qabs 0%Q) _).
    + exact (abl9_Qabs_wd _ _ Hz).
    + reflexivity.
  - exact He.
Qed.

(* —— 对齐二（实层·除法形端点改用 clamp）：件20 abl9_w_align 的旧      *)
(*   端点（乘法交换形）延拓至 clamp 代表元。证法=abl9_w_align（除法形   *)
(*   →乘法形）+real_mult_comm+对齐一 复合。                              *)
Lemma abl9b_int_w_align_clamp_57 :
  forall (x h : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (abl9b_wc x h Hd).
Proof.
  intros x h Hx Hh4 Hd.
  apply (real_eq_trans
          (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd) h)
          (abl9b_wc x h Hd)).
  - exact (abl9_w_align x h Hd).
  - apply (real_eq_trans
            (real_mult (real_inv_pos (real_plus real_one
                          (real_mult (real_plus x h) x)) Hd) h)
            (abl9b_w x h Hd)
            (abl9b_wc x h Hd)).
    + apply real_mult_comm.
    + exact (abl9b_int_w_clamp_real_eq_57 x h Hx Hh4 Hd).
Qed.

(* —— 对齐三（arctan 层·除法形端点改用 clamp）：件20                    *)
(*   abl9_arctan_wd_real 的 clamp 化改用——全域逐点等（除法形实参==w 实参， *)
(*   逐点成立，证明体内直构）仍由该件供给前一段，后一段接块一①运输件    *)
(*   接至 clamp 代表元。除法形与乘法形非定义相等（实参次序异），故两形域 *)
(*   证书 Hwd/Hw 各随其形入前件（装配期辅助实参形，诚实承载）。           *)
Lemma abl9b_int_atan_align_clamp_57 :
  forall (x h : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
    (Hwd : forall n : nat,
            QleT' (Qabs (projT1 (real_mult (real_plus (real_plus x h) (real_opp x))
                              (real_inv_pos (real_plus real_one
                                 (real_mult (real_plus x h) x)) Hd)) n)) 1)
    (Hw : forall n : nat,
           QleT' (Qabs (projT1 (abl9b_w x h Hd) n)) 1),
  real_eq (cauchy_real_arctan (real_mult (real_plus (real_plus x h) (real_opp x))
                                (real_inv_pos (real_plus real_one
                                   (real_mult (real_plus x h) x)) Hd)) Hwd)
          (cauchy_real_arctan (abl9b_wc x h Hd)
             (abl9b_w_clamp_dom (abl9b_w x h Hd))).
Proof.
  intros x h Hx Hh4 Hd Hwd Hw.
  apply (real_eq_trans
          (cauchy_real_arctan (real_mult (real_plus (real_plus x h) (real_opp x))
                             (real_inv_pos (real_plus real_one
                                (real_mult (real_plus x h) x)) Hd)) Hwd)
          (cauchy_real_arctan (abl9b_w x h Hd) Hw)
          (cauchy_real_arctan (abl9b_wc x h Hd)
             (abl9b_w_clamp_dom (abl9b_w x h Hd)))).
  - assert (Hpt : forall n : nat,
            projT1 (real_mult (real_plus (real_plus x h) (real_opp x))
                      (real_inv_pos (real_plus real_one
                         (real_mult (real_plus x h) x)) Hd)) n
            == projT1 (abl9b_w x h Hd) n).
    { intros n.
      unfold abl9b_w.
      rewrite (real_mult_proj (real_plus (real_plus x h) (real_opp x))
                 (real_inv_pos (real_plus real_one
                    (real_mult (real_plus x h) x)) Hd) n).
      rewrite (real_plus_proj (real_plus x h) (real_opp x) n).
      rewrite (real_plus_proj x h n).
      rewrite (real_opp_proj x n).
      rewrite (real_mult_proj h (real_inv_pos (real_plus real_one
                 (real_mult (real_plus x h) x)) Hd) n).
      cbn [projT1]. ring. }
    exact (abl9_arctan_wd_real
             (real_mult (real_plus (real_plus x h) (real_opp x))
                (real_inv_pos (real_plus real_one
                   (real_mult (real_plus x h) x)) Hd))
             (abl9b_w x h Hd) Hwd Hw Hpt).
  - exact (abl9b_int_retire_transport_57 x Hx h Hh4 Hd Hw).
Qed.

(* —— 3/4 代表元升界辅助引理：|w̃_n|≤3/4 ⟹ ≤1（cauchy_real_arctan 域证书*)
(*   恰为 ≤1 形；件53 全域证书 3/4 形与 arctan 域证书 1 形之间的必要     *)
(*   衔接件——内点链以 wc34 为 arctan 实参时的通用供给）。                *)
Lemma abl9b_int_w_clamp34_dom1_57 :
  forall (x h : Real)
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  forall n : nat,
  QleT' (Qabs (projT1 (abl9b_wc34 x h Hd) n)) 1.
Proof.
  intros x h Hd n.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (projT1 (abl9b_wc34 x h Hd) n)) (3 # 4) 1).
  - apply QleT'_to_Qle. exact (abl9b_w_clamp34_dom x h Hd n).
  - unfold Qle. simpl. lia.
Qed.

(* —— 对齐四（arctan 层·半径 3/4 变体）：件53 供给——内点链             *)
(*   w 侧基点 clamp 半径 3/4 代表元的 arctan 层实例（尾恒等由尾界        *)
(*   1/3<3/4，件30 w_bounds 尾形直接匹配 abl9b_wc34_id_pt；arctan 域证书由 *)
(*   升界辅助引理供给）。                                                *)
Lemma abl9b_int_atan_align_clamp34_57 :
  forall (x h : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)))
    (Hw : forall n : nat,
           QleT' (Qabs (projT1 (abl9b_w x h Hd) n)) 1),
  real_eq (cauchy_real_arctan (abl9b_w x h Hd) Hw)
          (cauchy_real_arctan (abl9b_wc34 x h Hd)
             (abl9b_int_w_clamp34_dom1_57 x h Hd)).
Proof.
  intros x h Hx Hh4 Hd Hw.
  destruct (abl9b_w_bounds x h Hx Hh4 Hd) as [Nw HNw].
  apply (abl9_arctan_arg_wd (abl9b_w x h Hd)
           (abl9b_wc34 x h Hd) Hw
           (abl9b_int_w_clamp34_dom1_57 x h Hd) Nw).
  intros n Hn.
  apply Qeq_sym.
  apply (abl9b_wc34_id_pt x h Hd n).
  destruct (HNw n (NatLe_lift _ _ Hn)) as [_ Hb13].
  exact (QleT'_to_Qle _ _ Hb13).
Qed.

(* —— 对齐五（实层衔接）：半径 1 与半径 3/4 两代表元尾域 real_eq        *)
(*   （同以 w 为尾域公共值；薄复合，诚实申明）。                          *)
Lemma abl9b_int_wc_wc34_real_eq_57 :
  forall (x h : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (abl9b_wc x h Hd) (abl9b_wc34 x h Hd).
Proof.
  intros x h Hx Hh4 Hd.
  apply (real_eq_trans (abl9b_wc x h Hd) (abl9b_w x h Hd)
                       (abl9b_wc34 x h Hd)).
  - apply real_eq_sym.
    exact (abl9b_int_w_clamp_real_eq_57 x h Hx Hh4 Hd).
  - apply real_eq_sym.
    exact (abl9b_wc34_w_real_eq x h Hx Hh4 Hd).
Qed.

(* ============================================================ *)
(* 块三 · S11 参数位装配骨架（记录装配包）                           *)
(*   参数位供给对照（逐行）：                                           *)
(*   ·x+Hx 逐点界：直接提供（装配入口同名参数直接传递）                *)
(*   ·eps+Heps：直接传递                                               *)
(*   ·delta 存在+0<delta：件30 δ 配方 min(min(1/4,d8/2),eps/16) 已证   *)
(*     （abl9b 体内，即 land_deriv 结论 sigT 首分量）                  *)
(*   ·h+|h|<delta→终近 1/4 需求：一行拆分（abl9b 体内 real_min 拆解，  *)
(*     L383-384 带已在链）                                             *)
(*   ·Hxh 逐点界：直接提供（同名直接传递）                             *)
(*   ·eps'+Heps'：直接传递                                             *)
(*   ·结论 raw 形 real_le（含斜率证书 b5a_one_plus_sq_pos 配形）：装配  *)
(*     产出（块一③迁移形直接使用）                                    *)
(*   ·Hd 证明项：abl9b_dom_pos x h Hx Hh4 零假设束直接提供（件30；A2 契约 *)
(*     语句面 w 证书位逐字承载，铁律见头注构造性注记③）               *)
(*   → 全参数位中唯一非直接提供项=A2 形主公式本体（主公式件进行中），即记录 *)
(*   首字段显式前件参数；主公式件证得后单点代入即得全包。               *)
(* ============================================================ *)

(* —— A2 形主公式语句面契约（固定 x 后的参数位型；=件30 Hdiff 参数位逐字， *)
(*   亦=件52 旧桥结论逐字）。主公式件 abl9_atan_diff_formula x Hx 闭合后 *)
(*   即本契约的 inhabitation。                                          *)
Definition abl9b_int_A2_formula_57 (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Set :=
  forall (h : Real) (Hh4 : real_lt (real_abs h) (real_const (1 # 4)))
    (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
             (real_opp (cauchy_real_arctan x Hx)))
          (cauchy_real_arctan (abl9b_wc x h (abl9b_dom_pos x h Hx Hh4))
             (abl9b_w_clamp_dom (abl9b_w x h (abl9b_dom_pos x h Hx Hh4)))).

(* —— S11 B5A_Item1B 参数位语句逐字契约（出节全称闭形；S11:L11855-11867*)
(*   带逐字，出节后即 inhabitation 目标型）。                            *)
Definition abl9b_int_deriv_sig_57 : Set :=
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                        (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* —— 两个出节使用件的实参化闭形语句面（S11 L12263-12274 带 /           *)
(*   L12531-12541 带逐字；出节后首参即参数位 inhabitation）。            *)
Definition abl9b_int_vdh_sig_57 : Set :=
  forall (x : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (eps : Real) (Heps : real_lt real_zero eps)
    (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  sigT (fun δa : Real => And (real_lt real_zero δa)
    (forall (h : Real), real_lt (real_abs h) δa ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).

Definition abl9b_int_sin_atan_sig_57 : Set :=
  forall (x : Real)
    (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x Hx h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).

(* —— 记录装配骨架：双字段。land_a2_formula：进行中供给                 *)
(*   （主公式件闭合后代入）；land_deriv：参数位逐字闭形                 *)
(*   （块一③迁移形装配产出）。出节使用件两闭形不入记录字段，作派生      *)
(*   定义：其语句面嵌 Q 序逐点界于存在束内，提取遇 prod-Prop 实例化     *)
(*   硬错。死墙实为 abl9b_int_sin_atan_closed_typed_57（sin_atan 支，   *)
(*   EXIT=1 独立复现）；vdh 支三命令形实测可抽（EXIT=0）；日志            *)
(*   abl9b_int_prep_57_final.log。非本件数学缺口，故提取判据取双字段包。 *)
Record abl9b_int_land_pack_57 : Type := mk_abl9b_int_land_pack_57 {
  land_a2_formula :
    forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
    abl9b_int_A2_formula_57 x Hx;
  land_deriv : abl9b_int_deriv_sig_57
}.

(* —— 装配主件：仅由进行中供给（A2 形主公式）构造骨架包。主公式件证得后单点 *)
(*   代入形：                                                            *)
(*   abl9b_int_land_pack_mk_57 (fun x Hx => abl9_atan_diff_formula x Hx) *)
(* 【陈旧申报勘注（abl9 陈旧申报勘注补录组）】上注『闭合后』条件已满足：主式已由 a2_56 L1871 A2 形闭合，代入位已由 abl9b_land_58.v L231–232 活码使用（abl9b_land_pack_installed_58）。本处条件登记旧文照录。 *)
(*   land_deriv 字段经块一③迁移形直接使用骨架 abl9b 产出（无桥无假设束）。 *)
Lemma abl9b_int_land_pack_mk_57 :
  forall (Ha2 : forall (x : Real)
             (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
             abl9b_int_A2_formula_57 x Hx),
  abl9b_int_land_pack_57.
Proof.
  intros Ha2.
  exact (mk_abl9b_int_land_pack_57 Ha2
    (fun (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
        (eps : Real) (Heps : real_lt real_zero eps) =>
       abl9b_int_assembly_direct_57 x Hx (Ha2 x Hx) eps Heps)).
Qed.

(* —— 出节使用件实参化闭形：以参数位闭形实参化，使用点证明              *)
(*   文本零改动（两处使用的均为参数位 inhabitation 本身，不感知其实现）。 *)
Definition abl9b_int_vdh_closed_57 (D : abl9b_int_deriv_sig_57) :=
  b5n_vdh_pts D.
Definition abl9b_int_sin_atan_closed_57 (D : abl9b_int_deriv_sig_57) :=
  b5a_sin_atan_diff D.

(* —— 签名符合性见证：注册契约（上方两 sig 定义，S11 L12263-12274 带 /  *)
(*   L12531-12541 带逐字重述）与闭形推断型定理级核对——重述若有出入，    *)
(*   此处即编译报错，不静默。                                            *)
Lemma abl9b_int_vdh_closed_typed_57 :
  forall D : abl9b_int_deriv_sig_57, abl9b_int_vdh_sig_57.
Proof.
  intros D.
  exact (abl9b_int_vdh_closed_57 D).
Qed.

Lemma abl9b_int_sin_atan_closed_typed_57 :
  forall D : abl9b_int_deriv_sig_57, abl9b_int_sin_atan_sig_57.
Proof.
  intros D.
  exact (abl9b_int_sin_atan_closed_57 D).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   核对三联：Lemma 名清单 12 = Qed 计数 12 = PA 语句 12，零差。        *)
(*   （另 Definition 6 + Record 1，无 Qed 面不计入核对。）              *)
(* ============================================================ *)
Print Assumptions abl9b_int_retire_transport_57.
Print Assumptions abl9b_int_hdiff_direct_57.
Print Assumptions abl9b_int_assembly_direct_57.
Print Assumptions abl9b_int_w_clamp_real_eq_57.
Print Assumptions abl9b_int_w_align_clamp_57.
Print Assumptions abl9b_int_atan_align_clamp_57.
Print Assumptions abl9b_int_w_clamp34_dom1_57.
Print Assumptions abl9b_int_atan_align_clamp34_57.
Print Assumptions abl9b_int_wc_wc34_real_eq_57.
Print Assumptions abl9b_int_land_pack_mk_57.
Print Assumptions abl9b_int_vdh_closed_typed_57.
Print Assumptions abl9b_int_sin_atan_closed_typed_57.

(* 提取检验（判据 = 输出 Obj.magic 计数 0；两检验目标均含于件52 已认证   *)
(* 检验目标内。出节使用件链的提取死墙登记见块三头注——非承认缺口。）      *)
Recursive Extraction abl9b_int_retire_transport_57.
Recursive Extraction abl9b_int_land_pack_mk_57.
