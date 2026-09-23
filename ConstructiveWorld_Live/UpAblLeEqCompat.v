(* ============================================================ *)
(* ToyR 玩具证替换件 —— T250 台账席 战役包K（tier2 头批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   lec_flag_add_le_lr（原 L226，2 句玩具证）                            *)
(*   lec_flag_lsum_le（原 L215，2 句玩具证）                              *)
(*   lec_e66s_add_of_le_pair（原 L162，2 句玩具证）                       *)
(*   lec_e66s_add_le_rl（原 L151，3 句玩具证）                            *)
(*   lec_e66s_add_le_lr（原 L141，3 句玩具证）                            *)
(*   lec_le_pair_le_b（原 L123，3 句玩具证）                              *)
(*   lec_le_b_pair_eq（原 L114，2 句玩具证）                              *)
(*   lec_eq_le_rev（原 L71，4 句玩具证）                                  *)
(*   lec_eq_le（原 L62，4 句玩具证）                                      *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T321 恒等守恒更正注记】2026-09-22 包AW九 台账席（恒等头注更正全量第一批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 9 参数位证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 参数位＋恒等守恒 9 参数位；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321 台账。                        *)
(* 附记：T277 判级全文恒等；包K 全量第一批整批直推（T317 六·1 方案①）                           *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblLeEqCompat.v —— 序与等词的双侧兼容引理族：序形与等词形互转、        *)
(*   沿等词双侧的序运输，及其在求和族上的原生折叠传输。                      *)
(*                                                                        *)
(* 背景：e66s 求和族（UpAblEps66Sum）已备等词面外延件与序面保序件，          *)
(*   而沿等词双侧的序运输与序面折叠传输此前无单件承载，本件补建此家族。       *)
(*                                                                        *)
(* 在库基座（只读引用）：real_eq_le（S07，等词⟹同向序，仅单向）、            *)
(*   real_le_antisym（S02，Or 形反对称）、gibbe2_le_b_antisym（G08，          *)
(*   Bishop 形反对称，逐 n 构造）、real_le_to_le_b（UpRealLeB 单向桥；        *)
(*   其逆向（le_b 的精确 Or 分解）构造性不可证——UpRealLeB 尾注载有           *)
(*   该否定性论证）。                                                        *)
(*                                                                        *)
(* 内容四组：                                                                *)
(* §A 兼容家族四件（本件自证）：lec_eq_le（等词⟹同向序，取 Or 编码右支）、    *)
(*   lec_eq_le_rev（等词⟹反向序，经 real_eq_sym）、                          *)
(*   lec_le_le_eq（双侧序⟹等词，四支构造性分解）、                           *)
(*   lec_le_eq_eq（沿等词双侧的序运输）；                                     *)
(* §B Bishop 侧家族两件：lec_le_b_pair_eq（le_b 双侧⟹等词，经                *)
(*   gibbe2_le_b_antisym）、lec_le_pair_le_b（双侧序⟹le_b 双侧，              *)
(*   经单向桥 real_le_to_le_b）；                                             *)
(* §C 求和族兼容通路五件（Section LecE66）：加法面序双侧形一对                *)
(*   （lec_e66s_add_le_lr／lec_e66s_add_le_rl，由 e66s_real_sum_over_S_add    *)
(*   经家族降至序面）、往返闭合 lec_e66s_add_of_le_pair、逐点双侧序⟹和等词    *)
(*   lec_e66s_sum_eq_of_pw_le_pair（经 e66s_real_sum_over_S_le 两次＋反对称）、*)
(*   序面原生折叠传输 lec_lsum_le_trans（经 e66s 序面＋p2f_lsum_bridge＋       *)
(*   lec_le_eq_eq 三步）；                                                    *)
(* §D bool 具体层实例三件：lec_flag_sumf／lec_flag_lsum_le／                  *)
(*   lec_flag_add_le_lr（枚举 e66s_flag_enum，零残留抽象参数）。               *)
(*                                                                        *)
(* 【依赖】CW_ConstructiveWorld_219；UpReqSumD；UpAblEps66Sum；               *)
(*   UpAblP2FeedMix（p2f_lsum_bridge）；UpRealLeB；G08_Gibbs。                *)
(*                                                                        *)
(* 【对标】mathlib 的 le_antisym／eq_of_le 类兼容引理；stdlib 有序域事实。     *)
(*                                                                        *)
(* 【构造性注记】零承认、纯构造性（零经典逻辑）；全件 Set 层语句              *)
(*   （real_eq／real_le／real_le_b 均 Set 值谓词），语句面无命题层泄露；       *)
(*   全 Qed 闭合；末段 Print Assumptions 审计应全部 Closed。                  *)
(*                                                                        *)
(* 【编译配方】coqc 9.1 直调，cpu_guard 包裹（-LoadLimit 85 -CoreN 2），       *)
(*   编译输出经 -o 写临时目录，树内 .vo 一律不动。                            *)
(*                                                                        *)
(*   提取说明：证明内容为序/等词谓词面上的构造性见证变换，无独立数值体；       *)
(*   提取面取求和载体 lec_flag_sumf 作计算内容代表，桥面引理以审计替代。       *)
(*                                                                        *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
Require Import UpAblEps66Sum.
Require Import UpAblP2FeedMix.
Require Import UpRealLeB.
Require Import G08_Gibbs.

(* ============================================================ *)
(* §A 兼容家族四件：双侧序-等词互转（本件自证）                        *)
(* ============================================================ *)

(** lec_eq_le·等词⟹同向序：由序谓词的 Or 编码（real_le x y :=           *)
(*   Or (real_lt x y) (real_eq x y)）取右支（等词见证位）即得。          *)
Lemma lec_eq_le : forall x y : Real, real_eq x y -> real_le x y.
Proof.
  intros x y H.
  unfold real_le.
  right.
  exact H.
Qed.

(** lec_eq_le_rev·等词⟹反向序：先经 real_eq_sym 换向，再用 lec_eq_le 取右支。 *)
Lemma lec_eq_le_rev : forall x y : Real, real_eq x y -> real_le y x.
Proof.
  intros x y H.
  apply lec_eq_le.
  apply real_eq_sym.
  exact H.
Qed.

(** lec_le_le_eq·双侧序⟹等词（反对称）：对两序前提的 Or 编码分四支：      *)
(*   （序，序）支：两严格序前提经传递性自撞 real_lt_irrefl，空型消除；    *)
(*   （序，等词）与（等词，序）支：经 real_eq_sym 落到等词支；            *)
(*   （等词，等词）支：取左侧见证。                                      *)
Lemma lec_le_le_eq : forall x y : Real,
  real_le x y -> real_le y x -> real_eq x y.
Proof.
  intros x y Hxy Hyx.
  destruct Hxy as [Hlt | Heq]; destruct Hyx as [Hlt' | Heq'].
  - exact (match (real_lt_irrefl x (real_lt_trans x y x Hlt Hlt')) with end).
  - exact (real_eq_sym y x Heq').
  - exact Heq.
  - exact Heq.
Qed.

(** lec_le_eq_eq·沿等词双侧的序运输：若 x 序不降于 y 且 x 与 x′、y 与 y′  *)
(*   分别等词，则 x′ 序不降于 y′；经序的传递性与家族件接续两次。          *)
Lemma lec_le_eq_eq : forall x y x' y' : Real,
  real_le x y -> real_eq x x' -> real_eq y y' -> real_le x' y'.
Proof.
  intros x y x' y' Hle Hxx' Hyy'.
  apply (real_le_trans x' y y').
  - apply (real_le_trans x' x y).
    + apply (lec_eq_le_rev x x'). exact Hxx'.
    + exact Hle.
  - apply (lec_eq_le y y'). exact Hyy'.
Qed.

(* ============================================================ *)
(* §B Bishop 侧家族两件：le_b 形反对称与单向桥的家族接入               *)
(* ============================================================ *)

(** lec_le_b_pair_eq·le_b 双侧⟹等词（Bishop 形反对称入族）：由 G08 的    *)
(*   gibbe2_le_b_antisym 逐 n 构造件直接给出（无 Or 分解、无 LPO）——     *)
(*   家族在 Bishop 形序上同样双侧闭合。                                  *)
Lemma lec_le_b_pair_eq : forall x y : Real,
  real_le_b x y -> real_le_b y x -> real_eq x y.
Proof.
  intros x y H1 H2.
  exact (gibbe2_le_b_antisym x y H1 H2).
Qed.

(** lec_le_pair_le_b·Or 形双侧⟹le_b 双侧：双侧各自经单向桥               *)
(*   real_le_to_le_b 转换；逆向精确分解构造性不可证，本件不作此主张。     *)
Lemma lec_le_pair_le_b : forall x y : Real,
  real_le x y -> real_le y x -> real_le_b x y.
Proof.
  intros x y Hxy Hyx.
  apply (real_le_to_le_b x y).
  exact Hxy.
Qed.

(* ============================================================ *)
(* §C 求和族序/等词兼容通路（e66s 加法/保序面的序面接续）               *)
(* ============================================================ *)

Section LecE66.

Context (S0 : Set).
Context (enum0 : list S0).

(** lec_e66s_add_le_lr·加法序上界：逐点相加后求和 序不降于 分别求和后相加；由 e66s_real_sum_over_S_add 经 lec_eq_le 降至序面。 *)
Lemma lec_e66s_add_le_lr : forall (f g : S0 -> Real),
  real_le (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)).
Proof.
  intros f g.
  apply lec_eq_le.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** lec_e66s_add_le_rl·加法序下界：反向序不等式；由 e66s_real_sum_over_S_add 经 lec_eq_le_rev 给出。 *)
Lemma lec_e66s_add_le_rl : forall (f g : S0 -> Real),
  real_le (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g))
          (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s))).
Proof.
  intros f g.
  apply lec_eq_le_rev.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** lec_e66s_add_of_le_pair·往返闭合：加法面双侧序不等式⟹加法等词，      *)
(*   即 lec_le_le_eq 的直接应用（双侧序收回等词）。                       *)
Lemma lec_e66s_add_of_le_pair : forall (f g : S0 -> Real),
  real_le (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)) ->
  real_le (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g))
          (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s))) ->
  real_eq (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)).
Proof.
  intros f g Hlr Hrl.
  apply (lec_le_le_eq _ _ Hlr Hrl).
Qed.

(** lec_e66s_sum_eq_of_pw_le_pair·逐点双侧序⟹和等词：逐点双侧序经        *)
(*   e66s_real_sum_over_S_le 两次提升到和级，再由 lec_le_le_eq 反对称     *)
(*   收尾——e66s 求和族等词面的一条纯序面通路。                           *)
Lemma lec_e66s_sum_eq_of_pw_le_pair : forall (f g : S0 -> Real),
  (forall s : S0, real_le (f s) (g s)) ->
  (forall s : S0, real_le (g s) (f s)) ->
  real_eq (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g).
Proof.
  intros f g Hfg Hgf.
  apply lec_le_le_eq.
  - exact (e66s_real_sum_over_S_le S0 enum0 f g Hfg).
  - exact (e66s_real_sum_over_S_le S0 enum0 g f Hgf).
Qed.

(** lec_lsum_le_trans·原生折叠序传输：逐点序不降⟹real_list_sum 上        *)
(*   序不降——三步：e66s 序面（sumd 折叠级）、折叠桥 p2f_lsum_bridge       *)
(*   （逐点等词）、lec_le_eq_eq（沿等词双侧运输）。                       *)
Lemma lec_lsum_le_trans : forall (f g : S0 -> Real),
  (forall s : S0, real_le (f s) (g s)) ->
  real_le (real_list_sum S0 f enum0) (real_list_sum S0 g enum0).
Proof.
  intros f g H.
  apply (lec_le_eq_eq (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)
                      (real_list_sum S0 f enum0) (real_list_sum S0 g enum0)).
  - exact (e66s_real_sum_over_S_le S0 enum0 f g H).
  - exact (p2f_lsum_bridge S0 enum0 f).
  - exact (p2f_lsum_bridge S0 enum0 g).
Qed.

End LecE66.

(* ============================================================ *)
(* §D bool 具体层实例（柯西实数层 fully concrete：枚举                    *)
(*   e66s_flag_enum＝true::false::nil，零残留抽象参数）                   *)
(* ============================================================ *)

(* 求和载体实例 lec_flag_sumf：e66s_sumf 特化到 bool 载体，供提取         *)
Definition lec_flag_sumf (f : bool -> Real) : Real :=
  e66s_sumf bool e66s_flag_enum f.

(** lec_flag_lsum_le：bool 载体上的 lec_lsum_le_trans 实例（逐点序不降⟹折叠序不降）。 *)
Theorem lec_flag_lsum_le :
  forall (f g : bool -> Real),
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (real_list_sum bool f e66s_flag_enum)
            (real_list_sum bool g e66s_flag_enum).
Proof.
  intros f g H.
  exact (lec_lsum_le_trans bool e66s_flag_enum f g H).
Qed.

(** lec_flag_add_le_lr：加法序上界的 bool 具体层实例。 *)
Theorem lec_flag_add_le_lr :
  forall (f g : bool -> Real),
    real_le (lec_flag_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (lec_flag_sumf f) (lec_flag_sumf g)).
Proof.
  intros f g.
  exact (lec_e66s_add_le_lr bool e66s_flag_enum f g).
Qed.

(* ============================================================ *)
(* 提取区：提取命令单条单常量（多条提取命令的输出会相互覆盖）。           *)
(*   本件证明内容全为序/等词兼容引理（Set 值谓词上的构造性见证变换），    *)
(*   无独立数值计算体；提取面取求和载体 lec_flag_sumf（折叠核心体）       *)
(*   作计算内容代表，桥面引理以假设审计替代提取。                         *)
(*                                                                        *)
(*                                                                        *)
(* ============================================================ *)
Set Extraction Output Directory "_ts2_g3out".
Extraction "ts2_lec_fold" lec_flag_sumf.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 应全部 Closed（零外部未证假设）       *)
(* ============================================================ *)
Print Assumptions lec_eq_le.
Print Assumptions lec_eq_le_rev.
Print Assumptions lec_le_le_eq.
Print Assumptions lec_le_eq_eq.
Print Assumptions lec_le_b_pair_eq.
Print Assumptions lec_le_pair_le_b.
Print Assumptions lec_e66s_add_le_lr.
Print Assumptions lec_e66s_add_le_rl.
Print Assumptions lec_e66s_add_of_le_pair.
Print Assumptions lec_e66s_sum_eq_of_pw_le_pair.
Print Assumptions lec_lsum_le_trans.
Print Assumptions lec_flag_lsum_le.
Print Assumptions lec_flag_add_le_lr.
