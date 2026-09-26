(* ===== ForwardKLAdjudication.v ===== *)
(* 席位 CZJ13（批次 E-STAGING-CZJ13）· T61b C8 前向 KL 族障碍账设计裁定登记件 · 2026-09-18 *)
(* 对象：ConstructiveWorld_Live/UpReqForwardKLFamily.v（席 Q6，GEO1 轨道缺 #1 前向 KL 族，
   7 件 fkl_ 前缀交付）头注三处挂账自判「结构性不达」——
   账 1 = :29、账 2 = :37、账 3 = :45（T61b-新增58件假设清点.md:87 C8 行）。
   本件逐账四要素裁定宣言（账位坐标/原叙事/结构性不达根因/替代真形引证）
   + 前向 KL 库内诚实形态三件套引证装配 + 结论段裁定词登记。
   格式对照：消融50/EntropyUnsatMark.v（CYE11 批C 形态核销宣言段）；
   判词格式对照：消融50/T62-零引用47枚triage.md B 类（语义承载永久槽，:41-:59）。 *)
(*
   【件形自判】本件为纯裁定登记件：零 Require 零新定理零声明——
   裁定件可以零新定理（任务书 C8 授权位），引用面逐一 grep/sed 实核防引虚件（§二/§四）；
   语句面 Set 层：无声明即无泄露面。转发收编位 fka_weak_triangle_ref 候闸登记（§四），
   按转发收编先例纪律（EntropyUnsatMark 对照：fa52 主件四关全绿入 vo_901 后方装 eum_ 转发件）
   被引主件未过闸不收编。
   【验证口径】G1 官方扫描器禁词=0（实测，--min-pa 0）；
   G2 = N/A（零 Require 零定理），另实测裸编译 EXIT=0（零依赖解析面，日志 Live/logs/czj13-g2-fka.log）。
*)

(* ========== 一、挂账原文：三账逐条四要素裁定宣言 ========== *)

(* ---- 账 1（前向 β 加权迭代步恒等）----
   要素 1 账位坐标：UpReqForwardKLFamily.v:29（头注【对偶表】条 1 挂账判词行）；
     挂账叙事源 = S05_AlignmentGRPO.v:3865 policy_iter_backward_kl_step_beta
     （β 加权三 KL 精确恒等，backward 基准系五件之首）。
   要素 2 原叙事：对 β 加权三 KL 迭代步恒等施加方向翻转 KL(p‖q) ↦ KL(q‖p)，
     得前向版 policy improvement 步恒等（强对偶叙事：翻转即得）。
   要素 3 结构性不达根因：前向迭代无 κ^t 收缩——翻转后 (1−η) 线性收缩因子
     变非线性因子，库内无对应恒等式引擎（:28-:29 原判词）；几何率领地
     UpReqIterGeomRate 为禁碰件（:63-:64 引擎链声明），非施工缺口。
   要素 4 替代真形引证：同席已成件 fkl_pt_split_flip（UpReqForwardKLFamily.v:141，
     方向翻转镜像诚实形，非平凡性[低]诚实标注）覆盖该方向的全部可证恒等面；
     β 加权迭代步叙事保留于 backward 基准系原件（S05:3865）不翻案。
     裁定：强对偶翻转叙事降级为镜像恒等叙事，非证明欠账。 *)

(* ---- 账 2（前向多步迭代收缩链）----
   要素 1 账位坐标：UpReqForwardKLFamily.v:37（头注【对偶表】条 4 挂账判词行）；
     挂账叙事源 = S05_AlignmentGRPO.v:4205 policy_iter_backward_kl_iter_le
     （迭代收缩链，≤ 形）。
   要素 2 原叙事：前向版多步迭代收缩链（κ^t 几何衰减率逐界收紧）。
   要素 3 结构性不达根因：同账 1——前向迭代无 κ^t 收缩（:37 原判词「同 1」）；
     库内前向链式恒等是加法形（残差逐步显式），无乘性收缩因子可累积；
     领地在飞勿碰（原注）。
   要素 4 替代真形引证：fkl_path_split_pt（UpReqForwardKLFamily.v:228）与
     fkl_path_split_sum（:258）给出链上每步/整链的精确加法恒等
     （Σ KL(f‖h) == Σ KL(f‖g) + Σ f·(log g − log h)）；
     多步聚合上界叙事由条件化弱三角 wtl_cond_triangle 接管（§二 件 1）——
     裁定：几何率叙事降级为加法链恒等 + 条件化上界叙事，可证面已闭合。 *)

(* ---- 账 3（无条件前向三角上界）----
   要素 1 账位坐标：UpReqForwardKLFamily.v:45（头注【附账】前向三角上界条，
     :44-:46；「定理化=挂账（障碍账）」原判词）；
     勘误史源 = UpReqWeakTriangle.v:10-18 方向声明段（EXP-D3B 任务书 c 定义
     假命题定谳与真形修正）。
   要素 2 原叙事：无条件前向三角不等式
     KL(p,r) ≤_B f(KL(p,q), KL(q,r))（无证书强三角叙事）。
   要素 3 结构性不达根因：残差无上界引擎——反向 Pinsker 不存在（:44-:45 原判词），
     链式恒等第三腿 E_p[log q − log r] 无定号（:34 同源判词），无条件 ≤ 形不闭合；
     实证面：EXP-D3 解析反例 Q=(1/2,1/2), R=(9/10,1/10), P=(0,1) 使
     RHS−LHS = ln(3/5) < 0（UpReqWeakTriangle.v:12-14 记载，近退化违反 77/3000）。
   要素 4 替代真形引证：wtl_cond_triangle（UpReqWeakTriangle.v:158，T61b 清点
     #279 已在库）——条件化弱三角真形
     KL(p‖r) ≤_B Σ KL(p‖q) + Σ KL(q‖r) + log(1/c)，证书 c·q_s ≤_real r_s，
     修正版压测 0/20000（:17-18 记载）。
     裁定：无证书强三角叙事降级为证书条件化叙事，可证面全闭合，非证明欠账。 *)

(* ========== 二、替代叙事装配：前向 KL 库内诚实形态三件套（引证实核记录） ========== *)
(* 三件套 = 条件化三角上界 + KL 非负 eps/B 引擎 + 残差显式恒等出口，
   构成前向 KL 在本库的诚实形态全谱；逐一 grep/sed 实核（防引虚件）：
   件 1 弱三角真形：UpReqWeakTriangle.v::wtl_cond_triangle（:158 Theorem 声明实读；
     :525 wtl_family sigT 封口；Q 层证书三件 wtl_qdiv_pos:81/wtl_min_ratio_lb:96/
     wtl_min_ratio_pos:116；T61b-新增58件假设清点.md:41 第 279 行登记）。
   件 2 Real 层 eps 形：S08_RealMainlineDPO.v:501 real_gibbs_inequality_eps
     （0 ≤ Σ_s kl(p s‖q s) + eps，real_le 形，:501 声明 sed 实读）；
     Bishop 封装 = UpRealLeB.v:600 real_gibbs_inequality_B（:612 内部直引 eps 件，
     sed 实读）——与 T62 triage #29（:55）「Real 层仅 eps/B 形可达」定谳互证。
   件 3 残差显式恒等形：UpReqForwardKLFamily.v:228 fkl_path_split_pt /
     :258 fkl_path_split_sum（KL(p‖r) == KL(p‖q) + E_p[log q − log r]，
     残差显式不隐藏；源件全文精读，四关面以其 vo 交付态为准）。 *)

(* ========== 三、结论段裁定词（对照 T62 B 类判词格式） ========== *)
(* 账 1 裁定词：前向 β 加权迭代步恒等=叙事降级而非证明欠账——翻转方向可证面
   已由 fkl_pt_split_flip 镜像诚实形覆盖，几何率叙事永久槽登记不入排程。
   账 2 裁定词：前向迭代收缩链=叙事降级而非证明欠账——加法链恒等
   （fkl_path_split_pt/sum）+ 条件化弱三角（wtl_cond_triangle）覆盖聚合上界可证面，
   κ^t 几何率叙事永久槽登记不入排程。
   账 3 裁定词：无条件前向三角上界=叙事降级而非证明欠账——证书条件化真形
   （wtl_cond_triangle，#279）覆盖三角上界可证面，无证书强三角叙事永久槽登记不入排程。
   总判：三账根因皆引擎级（无 κ^t 收缩引擎、无反向 Pinsker/残差上界引擎），
   非施工级；库内诚实形态三件套已覆盖其全部可证面，三账所欠者非「证明」
   而是「无条件强叙事」——该叙事在本库构造性 Set 层纪律下不可满足。
   谱系附记：与 T62-零引用47枚triage.md B 类 #29-32 墙族（G07 KL 墙族，
   req/无条件层不可达、eps/条件化层可达）同谱系同判词，零翻案；
   处置=登记永久槽不入排程（对照 T62 B 类「语义承载永久槽」判词格式）。 *)

(* ========== 四、转发收编位候闸登记（fka_weak_triangle_ref） ========== *)
(* 触发条件勘定（任务书：WeakTriangleClose.v 已落盘且可 Require 方出转发定理）：
   ① 已落盘 ✓：消融50/WeakTriangleClose.v（CZH13，T61b C6 收口件）于本席窗口
     落盘，391 行；勘定结论：主件 wtc_weak_triangle_load（:357，结论面=wtc_cs2_real
     :330 逐字）、sigT 封口 wtc_family（:375）、四要素核销宣言头注（:33-:44）、
     文尾 Print Assumptions 审计位（:383-:390）齐备，件形完整。
     注意其内容为弱三角领地 G3 CS 权渡腿收口（二元 Gram 核 (Σab)^2 ≤ Σa^2·Σb^2），
     非 KL 弱三角真形本体（真形=§二 件 1 wtl_cond_triangle），收编时引证须分工如实。
   ② 可 Require ✗：本地双信任根实测均墙（倒墙定格）：
     · ConstructiveWorld_vo 根：S01_BaseRing.vo / UpReqWeakTriangle.vo 皆报
       「makes inconsistent assumptions over Corelib.Init.Prelude」（外来编译器
       幻数墙；探针 probe_wtl 定格，日志 Live/logs/czj13-side-*.log）；
     · Live/vorebuild_901 活基座：S01_BaseRing.vo 报「inconsistent assumptions
       over Stdlib.QArith.QArith」（对齐重编管线在飞未收敛段）；
     · fa53_compat_abs.vo 两根皆缺，侧编链断于第一跳。
   ③ 处置：按转发收编先例纪律（被引主件过闸方收编）本席不装转发定理，
     fka_weak_triangle_ref 登记候闸，装法定格如下（候闸后一跳可装）：
       Require Import S01_BaseRing. Require Import fa53_compat_abs.
       Require Import WeakTriangleClose.
       Theorem fka_weak_triangle_ref :
         forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI)
                (a b c d : R),
           le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
              (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
       Proof. exact wtc_weak_triangle_load. Qed.
     （fka_ 前缀全库零撞名：ConstructiveWorld_Live / 消融50 / Live/vorebuild_901
       三树 grep 实测零命中，2026-09-18。）
   红线自审：零 Require 零新定理零声明（纯裁定登记面）；零云端零 git；
   原树只读（ConstructiveWorld_Live 仅读）；本件只写 消融50/。 *)
