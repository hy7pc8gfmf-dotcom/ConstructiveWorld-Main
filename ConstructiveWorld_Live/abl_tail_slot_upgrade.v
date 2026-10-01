(* ==========================================================================)
   abl_tail_slot_upgrade.v — 独立槽批·部分供形升级件
   ── 使命：非 W-IDPIN-01/W-LPO-ADJ-01 两项在册阻隔位的独立槽批，逐槽现档实读
      「部分供形弱于槽形的差一步」，按四类升级配方（绑定名差／前提强弱差／结论方向差／
      特化缺失）出升级供给定理，部分供形升为槽面全形。选槽六位＋使用面喂形三位：
      （一）非空 Id 面槽族三位——P7BoundedSoftmaxDeep.v:161/:374、Arch_Up_01.v:272，
      升级配方＝fa56b_cons_nil_id_contra 判别核的去前件泛化：forall T (x : T)
      (rest : list T), Not (Id (cons x rest) nil)，槽面在 enum := x::rest 时逐字退化入位；
      （二）非空 eq 面槽一位——UpAblP2WByPass.v:111，同款泛 cons 形于 eq 面；面归属
      机器可检（Printing All 实测该表达式整体 Set 面排序，非 Prop 语句面）；
      （三）配分两桥槽两位——Arch_PA_04.v:910-914/:915-917，升级配方＝
      logc_energy_in_log_boltzmann／logc_free_energy_boltzmann 双引擎直引＋sup_compat
      证书转写一步（正性证书位系不透明 Qed 件，经 sup_compat x y Hx Hy (req_refl x)
      逐点转写传入槽面）；使用面喂形三位＝Arch_Up_01.v:327 N_R_pos 的 cons 形实例闭形
      （kvev_list_len_pos 直接代入）、Arch_PA_04.v:1108-1110/:1147-1157 出节全参重述。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqLogCompD（logc_ 双引擎）、
      Arch_Up_01（kvev_list_len_pos 使用根件）、Arch_PA_04（cwe_* 节内定义与两使用定理）、
      Stdlib List、Stdlib Extraction——全部只读引用；目标五件零字节不动、零级联。
   ── 对标行：判别核＝fa56b_cons_nil_id_contra@ToyR_fa56b_ext.v:203-208（本件零 Require
      该件，判别核自持重演）；bool 二点列实例形＝uazlr_ne_bool_two@UpAblP6_ZPosLowRef.v:55；
      eq 面槽使用根＝sumd_sum_pos@UpReqSumD.v:328-335；双引擎＝logc_energy_in_log_boltzmann@
      UpReqLogCompD.v:353-356／logc_free_energy_boltzmann@:627-631；Real 实例闭形先例＝
      bbridge_energy_in_log_boltzmann_bridge@BBDBridgeSupply.v:112-124；填位具名制＝abl_tail_supply_68.v；出节全参喂形制＝abl_tail_supply_66.v。
   ── 构造性注记：全件零承认式声明、零悬置前提、零经典逻辑；语句面承载位全 Set 形；
      本文件零节内假设申报位；供给定理只使用已编内容，零接口外新前提；十二定理前提面
      审计取全 Closed 判据；提取检验取 Obj.magic 计数判据，另设对照命令并排提取比对计数
      （G3 对照实验口径，如实登记禁虚报）。
   ── 编译配方：单道 nice -19 rocq c -native-compiler no -Q <统一缓存根> "" abl_tail_slot_upgrade.v；
      绿判：EXIT=0／日志真错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v。
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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqLogCompD.
Require Import Arch_Up_01.
Require Import Arch_PA_04.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 一、非空 Id 面槽族（覆盖图 🟡 三位：P7B:161／P7B:374／Up_01:272） *)
(*   差异＝特化缺失（实例形在役、泛 cons 形缺位）＋前提强弱差         *)
(*   （fa56b_cons_nonempty 带尾表非空前件）。判别核自持重演           *)
(*   （fa56b_cons_nil_id_contra 同款 match 项，零 Require 耦合）。   *)
(* ============================================================ *)

(* 判别核载体：列表构造子分裂载体（nil 支单位型、cons 支空型） *)
Definition tspu_ne_case (T : Set) (l : list T) : Set :=
  match l with
  | nil => unit
  | _ => Empty_set
  end.

(* ---- 升级供给本体：非空 Id 面泛 cons 形（P7B:161/:374 槽面在       *)
(*      enum := x::rest 时逐字退化入位；S01 Not/Id 全 Set 面序） ---- *)
Theorem tspu_ne_cons_id : forall (T : Set) (x : T) (rest : list T),
  S01_BaseRing.Not (S01_BaseRing.Id (cons x rest) (@nil T)).
Proof.
  intros T x rest H.
  exact (match S01_BaseRing.id_sym H in S01_BaseRing.Id _ a
         return tspu_ne_case T a with
         | S01_BaseRing.id_refl => tt
         end).
Qed.

(* ---- 覆盖图实例锚形具名：bool 二点列（uazlr_ne_bool_two 同语句的    *)
(*      Id 面读法；特化缺失一环由本体一击补齐） ---- *)
Theorem tspu_ne_bool_two_id :
  S01_BaseRing.Not (S01_BaseRing.Id (true :: false :: nil) (@nil bool)).
Proof.
  exact (tspu_ne_cons_id bool true (false :: nil)).
Qed.

(* ---- 目标位具名一：P7BoundedSoftmaxDeep.v:161（段三 P7DNoSwap 节） ---- *)
Theorem tspu_p7b3_enum_nonempty : forall (T : Set) (x : T) (rest : list T),
  S01_BaseRing.Not (S01_BaseRing.Id (cons x rest) (@nil T)).
Proof.
  intros T x rest.
  exact (tspu_ne_cons_id T x rest).
Qed.

(* ---- 目标位具名二：P7BoundedSoftmaxDeep.v:374（段七节） ---- *)
Theorem tspu_p7b7_enum_nonempty : forall (T : Set) (x : T) (rest : list T),
  S01_BaseRing.Not (S01_BaseRing.Id (cons x rest) (@nil T)).
Proof.
  intros T x rest.
  exact (tspu_ne_cons_id T x rest).
Qed.

(* ---- 目标位具名三：Arch_Up_01.v:272（KVEv 节 states_ne 命题位） ---- *)
Theorem tspu_up01_states_ne : forall (T : Set) (x : T) (rest : list T),
  S01_BaseRing.Not (S01_BaseRing.Id (cons x rest) (@nil T)).
Proof.
  intros T x rest.
  exact (tspu_ne_cons_id T x rest).
Qed.

(* ---- 使用面喂形：Arch_Up_01.v:327 N_R_pos（kvev_list_len_pos 使用   *)
(*      根件直接代入）的 cons 形状态表实例闭形 ---- *)
Theorem tspu_up01_nR_pos_cons :
  forall (T : Set) (x : T) (rest : list T),
    real_lt real_zero (real_of_nat (length (cons x rest))).
Proof.
  intros T x rest.
  exact (kvev_list_len_pos T (cons x rest) (tspu_ne_cons_id T x rest)).
Qed.

(* ============================================================ *)
(* 二、非空 eq 面槽（覆盖图 🟡 一位：P2W:111 SlqSumD 节）              *)
(*   差异＝特化缺失（uazlr_ne_bool_two:55 bool 二点列实例形在役，泛     *)
(*   cons 形缺位）。面归属机器可检＝提取检验 Printing All 实测该表达式整体      *)
(*   Set 面排序（Not 取 S01 读法），非 Prop 语句面；升级配方＝同款      *)
(*   泛 cons 形于 eq 面，槽使用根 sumd_sum_pos（UpReqSumD:328 非空     *)
(*   前件与 :111 槽面同款表达式、SlqSumD :124 直接代入实证）逐字兼容。      *)
(* ============================================================ *)

(* ---- 升级供给本体：非空 eq 面泛 cons 形 ---- *)
Theorem tspu_ne_cons_eq : forall (T : Set) (x : T) (rest : list T),
  Not (cons x rest = nil).
Proof.
  intros T x rest H.
  discriminate H.
Qed.

(* ---- 目标位具名四：UpAblP2WByPass.v:111（SlqSumD 节 enum0_nonempty） ---- *)
Theorem tspu_p2w_enum0_nonempty : forall (T : Set) (x : T) (rest : list T),
  Not (cons x rest = nil).
Proof.
  intros T x rest.
  exact (tspu_ne_cons_eq T x rest).
Qed.

(* ============================================================ *)
(* 三、配分两桥槽（覆盖图 🟡 两位：Arch_PA_04:910-914／:915-917，      *)
(*    ReqFreeEnergyPilot 节；覆盖图 §三 R5 公共件口径——只做            *)
(*    「logc_ 引擎＋G05 入位」一端公共件一件，禁两桥各证一遍）。        *)
(*    差异＝Real 实例闭形在役（BBDBridgeSupply:112/:133）而泛 RIS 形    *)
(*    差一步；升级配方＝双引擎直引＋sup_compat 证书转写。               *)
(* ============================================================ *)

Section TspuPa04Bridge.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Variable sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Variable sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Variable sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Variable fep_partition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Variable sup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Variable sup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* ---- 升级供给一：能量入对数恒等式（PA_04:910-914 槽面逐字；        *)
(*      证＝logc_energy_in_log_boltzmann 引擎直引＋sup_compat 证书     *)
(*      转写一步：logc_boltz 与 cwe_boltzmann_dist 定义体逐字同体       *)
(*      双透明可转换，正性证书两位系不透明 Qed 件，经 sup_compat        *)
(*      x y Hx Hy (req_refl x) 逐点转写传入槽面；全参显式零通配）。 ---- *)
Theorem tspu_pa04_energy_in_log_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                               (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  apply (req_trans (base_loss s)
                   (opp (mult D (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                          (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                                      (log Z Z_pos))))
                   (opp (mult D (plus (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                           (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                                      (log Z Z_pos))))).
  - exact (logc_energy_in_log_boltzmann S base_loss D D_pos Z Z_pos
             sup_compat sup_log_exp_neg s).
  - exact (req_opp_compat
             (mult D (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))
             (mult D (plus (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))
             (req_mult_compat D D
                (plus (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                           (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                      (log Z Z_pos))
                (plus (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                           (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                      (log Z Z_pos))
                (req_refl D)
                (req_plus_compat
                   (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                        (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                   (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                        (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                   (log Z Z_pos) (log Z Z_pos)
                   (sup_compat (logc_boltz S base_loss D D_pos Z Z_pos s)
                               (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                               (logc_boltz_pos S base_loss D D_pos Z Z_pos s)
                               (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s)
                               (req_refl (logc_boltz S base_loss D D_pos Z Z_pos s)))
                   (req_refl (log Z Z_pos))))).
Qed.

(* ---- 升级供给二：自由能显式式（PA_04:915-917 槽面逐字；证＝        *)
(*      logc_free_energy_boltzmann 引擎直引＋cwe_free_energy 与        *)
(*      logc_fe 逐字同体展开＋sum_ext 逐点 sup_compat 转写）。 ---- *)
Theorem tspu_pa04_free_energy_bridge :
  req (@SigMigrate.cwe_free_energy R RIS S sumf base_loss D
         (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos)
         (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos))
      (mult (opp D) (log Z Z_pos)).
Proof.
  apply (req_trans
           (@SigMigrate.cwe_free_energy R RIS S sumf base_loss D
              (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos)
              (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos))
           (logc_fe S sumf base_loss D
              (logc_boltz S base_loss D D_pos Z Z_pos)
              (logc_boltz_pos S base_loss D D_pos Z Z_pos))
           (mult (opp D) (log Z Z_pos))).
  - unfold SigMigrate.cwe_free_energy, logc_fe.
    exact (req_plus_compat
             (sumf (fun s : S => mult (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                      (base_loss s)))
             (sumf (fun s : S => mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                                      (base_loss s)))
             (mult D (sumf (fun s : S => mult (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                              (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                                   (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s)))))
             (mult D (sumf (fun s : S => mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                                              (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                                   (logc_boltz_pos S base_loss D D_pos Z Z_pos s)))))
             (req_refl (sumf (fun s : S => mult (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                                (base_loss s))))
             (req_mult_compat D D
                (sumf (fun s : S => mult (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                         (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                              (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))))
                (sumf (fun s : S => mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                                         (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                              (logc_boltz_pos S base_loss D D_pos Z Z_pos s))))
                (req_refl D)
                (sum_ext
                   (fun s : S => mult (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                      (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                           (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s)))
                   (fun s : S => mult (logc_boltz S base_loss D D_pos Z Z_pos s)
                                      (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                                           (logc_boltz_pos S base_loss D D_pos Z Z_pos s)))
                   (fun s : S => req_mult_compat
                      (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                      (logc_boltz S base_loss D D_pos Z Z_pos s)
                      (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                           (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))
                      (log (logc_boltz S base_loss D D_pos Z Z_pos s)
                           (logc_boltz_pos S base_loss D D_pos Z Z_pos s))
                      (req_refl (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s))
                      (sup_compat (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                  (logc_boltz S base_loss D D_pos Z Z_pos s)
                                  (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s)
                                  (logc_boltz_pos S base_loss D D_pos Z Z_pos s)
                                  (req_refl (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s))))))).
  - exact (logc_free_energy_boltzmann S sumf sum_ext sum_add sum_linear
             base_loss D D_pos Z Z_pos fep_partition sup_compat sup_log_exp_neg).
Qed.

(* ---- 使用面喂形一：req_p_times_energy_decomp（PA_04:1108-1110）     *)
(*      出节全参，能量桥位以升级供给一入位消失、余参全数保留。 ---- *)
Theorem tspu_pa04_p_times_energy_decomp_wo :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s))
        (plus (opp (mult D (mult (p s) (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                            (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s)))))
              (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  exact (@SigMigrate.req_p_times_energy_decomp R RIS S base_loss D D_pos Z Z_pos
           (fun s0 : S => tspu_pa04_energy_in_log_bridge s0) p s).
Qed.

(* ---- 使用面喂形二：req_free_energy_kl_decomp（PA_04:1147-1157，     *)
(*      件内自证的迁移试点主定理）出节全参，双桥位以升级供给一/二       *)
(*      入位消失、余参全数保留。 ---- *)
Theorem tspu_pa04_free_energy_kl_decomp_wo :
  forall (p : S -> R) (Hp : @SigMigrate.cwe_normalized R RIS S sumf p)
    (p0 : @SigMigrate.cwe_positive_dist R RIS S p),
    req (@SigMigrate.cwe_free_energy R RIS S sumf base_loss D p p0)
        (plus (@SigMigrate.cwe_free_energy R RIS S sumf base_loss D
                 (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos)
                 (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos))
              (mult D (sumf (fun s : S =>
                mult (p s)
                  (SigMigrate.rminus (log (p s) (p0 s))
                                     (log (@SigMigrate.cwe_boltzmann_dist R RIS S base_loss D D_pos Z Z_pos s)
                                          (@SigMigrate.req_boltzmann_positive R RIS S base_loss D D_pos Z Z_pos s))))))).
Proof.
  intros p Hp p0.
  exact (@SigMigrate.req_free_energy_kl_decomp R RIS S sumf sum_ext sum_add sum_linear
           base_loss D D_pos Z Z_pos
           (fun s0 : S => tspu_pa04_energy_in_log_bridge s0)
           tspu_pa04_free_energy_bridge p Hp p0).
Qed.

End TspuPa04Bridge.

(* ============================================================ *)
(* 四、PA 审计段（对照 Check 读面＋逐件 Closed 判读）                   *)
(* ============================================================ *)

(* 对照 Check：根件与引擎语句面读出（面型保真对照留痕） *)
Check tspu_ne_cons_id.
Check tspu_ne_cons_eq.
Check kvev_list_len_pos.
Check logc_energy_in_log_boltzmann.
Check logc_free_energy_boltzmann.
Check @SigMigrate.cwe_boltzmann_dist.
Check @SigMigrate.req_boltzmann_positive.

(* 前提面审计（逐件全 Closed 判据；名清单＝Qed 计数＝12，零差） *)
Print Assumptions tspu_ne_cons_id.
Print Assumptions tspu_ne_bool_two_id.
Print Assumptions tspu_p7b3_enum_nonempty.
Print Assumptions tspu_p7b7_enum_nonempty.
Print Assumptions tspu_up01_states_ne.
Print Assumptions tspu_up01_nR_pos_cons.
Print Assumptions tspu_ne_cons_eq.
Print Assumptions tspu_p2w_enum0_nonempty.
Print Assumptions tspu_pa04_energy_in_log_bridge.
Print Assumptions tspu_pa04_free_energy_bridge.
Print Assumptions tspu_pa04_p_times_energy_decomp_wo.
Print Assumptions tspu_pa04_free_energy_kl_decomp_wo.

(* ============================================================ *)
(* 五、提取检验区（判据＝Obj.magic 库层转写与本件引入分开计数如实登记；  *)
(*   输出目录为本池检验区；对照命令提取库件原身并排比对——G3 对照实验）  *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Require Import ToyR_fa56b_ext.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspu_ne_cons_id tspu_ne_cons_eq tspu_up01_nR_pos_cons.
Recursive Extraction tspu_pa04_energy_in_log_bridge.
Recursive Extraction tspu_pa04_free_energy_bridge.
(* 对照实验：库件原身单独提取（归桶基线；末件＝库内同款判别核，       *)
(*   归桶判据＝其提取体 Obj.magic 同形复现即本件引入段为判别核固有     *)
(*   依赖消去转写，非承认前提引入） *)
Recursive Extraction kvev_list_len_pos.
Recursive Extraction SigMigrate.req_boltzmann_positive.
Recursive Extraction fa56b_cons_nil_id_contra.

(* 终验实测登记（实测在案，禁虚报）：
   ① 编译 EXIT=0 绿、日志真错行 0；提取命令 EXIT=0 绿（bypass opacity
     提示为库层 Qed 常量体披露警告面，非错误行，66 件先例同款）。
   ② Obj.magic 计 2 行（grep 计行数），分段归因（对照实验口径）：
     本件引入段 1 处——tspu_ne_cons_id 体内判别核（match id_sym H in
     Id _ a return tspu_ne_case T a 依赖消去项）的提取器型别转写
     （提取输出 :800 Obj.magic Tt；运行时恒等于 Tt 单元值，非悬置前提
     引入）；对照基线段 1 处——对照命令提取库内同款判别核
     fa56b_cons_nil_id_contra 原身，其提取体 :5538 同形 Obj.magic Tt
     复现＝本件 1 处归桶判据成立（判别核固有依赖消去转写，库件原身
     同款）。其余提取段（eq 面纯项体、kvev 使用根、PA_04 SigMigrate
     闭包段）实测 Obj.magic 计 0。前提面审计 12 件全 Closed 为独立
     证据。eq 面
     tspu_ne_cons_eq 提取体为 absurd case 纯项、零 Obj.magic；两桥与
     两使用面喂形提取段（PA_04 SigMigrate 闭包段）实测 Obj.magic 计 0。
   ③ PA 审计十二件全 Closed（Closed under the global context 计 12＝
     Qed 计数 12，零差）。
   ④ G4 第五证：rocq check -o EXIT=0（日志 _log/
     abl_tail_slot_upgrade-coqchk.log），公理/type-in-type/
     unsafe fixpoints/positivity assumed 全位 none，本件 12 常量逐被核。
   ⑤ 道闸：起编前 ps 计 0，单道顺序。 *)
