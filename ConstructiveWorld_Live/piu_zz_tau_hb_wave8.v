(* piu_zz_tau_hb_wave8.v — KB11 Hb 升格候选子片 8/8（1024 段 Hb80-Hb95·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave8.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L2699-L2719 (assert Hb80) *)
Lemma piu_zz_hb_1024_80 : piu_zz_zprod_seg 1024%nat (512%nat + 240%nat) 16%nat = ((if zz_in_Pn 1024 753%nat then Z.of_nat 753%nat else 1%Z) * ((if zz_in_Pn 1024 754%nat then Z.of_nat 754%nat else 1%Z) * ((if zz_in_Pn 1024 755%nat then Z.of_nat 755%nat else 1%Z) * ((if zz_in_Pn 1024 756%nat then Z.of_nat 756%nat else 1%Z) * ((if zz_in_Pn 1024 757%nat then Z.of_nat 757%nat else 1%Z) * ((if zz_in_Pn 1024 758%nat then Z.of_nat 758%nat else 1%Z) * ((if zz_in_Pn 1024 759%nat then Z.of_nat 759%nat else 1%Z) * ((if zz_in_Pn 1024 760%nat then Z.of_nat 760%nat else 1%Z) * ((if zz_in_Pn 1024 761%nat then Z.of_nat 761%nat else 1%Z) * ((if zz_in_Pn 1024 762%nat then Z.of_nat 762%nat else 1%Z) * ((if zz_in_Pn 1024 763%nat then Z.of_nat 763%nat else 1%Z) * ((if zz_in_Pn 1024 764%nat then Z.of_nat 764%nat else 1%Z) * ((if zz_in_Pn 1024 765%nat then Z.of_nat 765%nat else 1%Z) * ((if zz_in_Pn 1024 766%nat then Z.of_nat 766%nat else 1%Z) * ((if zz_in_Pn 1024 767%nat then Z.of_nat 767%nat else 1%Z) * (if zz_in_Pn 1024 768%nat then Z.of_nat 768%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_768.
    rewrite piu_zz_inPn_1024_767.
    rewrite piu_zz_inPn_1024_766.
    rewrite piu_zz_inPn_1024_765.
    rewrite piu_zz_inPn_1024_764.
    rewrite piu_zz_inPn_1024_763.
    rewrite piu_zz_inPn_1024_762.
    rewrite piu_zz_inPn_1024_761.
    rewrite piu_zz_inPn_1024_760.
    rewrite piu_zz_inPn_1024_759.
    rewrite piu_zz_inPn_1024_758.
    rewrite piu_zz_inPn_1024_757.
    rewrite piu_zz_inPn_1024_756.
    rewrite piu_zz_inPn_1024_755.
    rewrite piu_zz_inPn_1024_754.
    rewrite piu_zz_inPn_1024_753.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2720-L2740 (assert Hb81) *)
Lemma piu_zz_hb_1024_81 : piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) 16%nat = ((if zz_in_Pn 1024 737%nat then Z.of_nat 737%nat else 1%Z) * ((if zz_in_Pn 1024 738%nat then Z.of_nat 738%nat else 1%Z) * ((if zz_in_Pn 1024 739%nat then Z.of_nat 739%nat else 1%Z) * ((if zz_in_Pn 1024 740%nat then Z.of_nat 740%nat else 1%Z) * ((if zz_in_Pn 1024 741%nat then Z.of_nat 741%nat else 1%Z) * ((if zz_in_Pn 1024 742%nat then Z.of_nat 742%nat else 1%Z) * ((if zz_in_Pn 1024 743%nat then Z.of_nat 743%nat else 1%Z) * ((if zz_in_Pn 1024 744%nat then Z.of_nat 744%nat else 1%Z) * ((if zz_in_Pn 1024 745%nat then Z.of_nat 745%nat else 1%Z) * ((if zz_in_Pn 1024 746%nat then Z.of_nat 746%nat else 1%Z) * ((if zz_in_Pn 1024 747%nat then Z.of_nat 747%nat else 1%Z) * ((if zz_in_Pn 1024 748%nat then Z.of_nat 748%nat else 1%Z) * ((if zz_in_Pn 1024 749%nat then Z.of_nat 749%nat else 1%Z) * ((if zz_in_Pn 1024 750%nat then Z.of_nat 750%nat else 1%Z) * ((if zz_in_Pn 1024 751%nat then Z.of_nat 751%nat else 1%Z) * (if zz_in_Pn 1024 752%nat then Z.of_nat 752%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_752.
    rewrite piu_zz_inPn_1024_751.
    rewrite piu_zz_inPn_1024_750.
    rewrite piu_zz_inPn_1024_749.
    rewrite piu_zz_inPn_1024_748.
    rewrite piu_zz_inPn_1024_747.
    rewrite piu_zz_inPn_1024_746.
    rewrite piu_zz_inPn_1024_745.
    rewrite piu_zz_inPn_1024_744.
    rewrite piu_zz_inPn_1024_743.
    rewrite piu_zz_inPn_1024_742.
    rewrite piu_zz_inPn_1024_741.
    rewrite piu_zz_inPn_1024_740.
    rewrite piu_zz_inPn_1024_739.
    rewrite piu_zz_inPn_1024_738.
    rewrite piu_zz_inPn_1024_737.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2741-L2761 (assert Hb82) *)
Lemma piu_zz_hb_1024_82 : piu_zz_zprod_seg 1024%nat (512%nat + 208%nat) 16%nat = ((if zz_in_Pn 1024 721%nat then Z.of_nat 721%nat else 1%Z) * ((if zz_in_Pn 1024 722%nat then Z.of_nat 722%nat else 1%Z) * ((if zz_in_Pn 1024 723%nat then Z.of_nat 723%nat else 1%Z) * ((if zz_in_Pn 1024 724%nat then Z.of_nat 724%nat else 1%Z) * ((if zz_in_Pn 1024 725%nat then Z.of_nat 725%nat else 1%Z) * ((if zz_in_Pn 1024 726%nat then Z.of_nat 726%nat else 1%Z) * ((if zz_in_Pn 1024 727%nat then Z.of_nat 727%nat else 1%Z) * ((if zz_in_Pn 1024 728%nat then Z.of_nat 728%nat else 1%Z) * ((if zz_in_Pn 1024 729%nat then Z.of_nat 729%nat else 1%Z) * ((if zz_in_Pn 1024 730%nat then Z.of_nat 730%nat else 1%Z) * ((if zz_in_Pn 1024 731%nat then Z.of_nat 731%nat else 1%Z) * ((if zz_in_Pn 1024 732%nat then Z.of_nat 732%nat else 1%Z) * ((if zz_in_Pn 1024 733%nat then Z.of_nat 733%nat else 1%Z) * ((if zz_in_Pn 1024 734%nat then Z.of_nat 734%nat else 1%Z) * ((if zz_in_Pn 1024 735%nat then Z.of_nat 735%nat else 1%Z) * (if zz_in_Pn 1024 736%nat then Z.of_nat 736%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_736.
    rewrite piu_zz_inPn_1024_735.
    rewrite piu_zz_inPn_1024_734.
    rewrite piu_zz_inPn_1024_733.
    rewrite piu_zz_inPn_1024_732.
    rewrite piu_zz_inPn_1024_731.
    rewrite piu_zz_inPn_1024_730.
    rewrite piu_zz_inPn_1024_729.
    rewrite piu_zz_inPn_1024_728.
    rewrite piu_zz_inPn_1024_727.
    rewrite piu_zz_inPn_1024_726.
    rewrite piu_zz_inPn_1024_725.
    rewrite piu_zz_inPn_1024_724.
    rewrite piu_zz_inPn_1024_723.
    rewrite piu_zz_inPn_1024_722.
    rewrite piu_zz_inPn_1024_721.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2762-L2782 (assert Hb83) *)
Lemma piu_zz_hb_1024_83 : piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 16%nat = ((if zz_in_Pn 1024 705%nat then Z.of_nat 705%nat else 1%Z) * ((if zz_in_Pn 1024 706%nat then Z.of_nat 706%nat else 1%Z) * ((if zz_in_Pn 1024 707%nat then Z.of_nat 707%nat else 1%Z) * ((if zz_in_Pn 1024 708%nat then Z.of_nat 708%nat else 1%Z) * ((if zz_in_Pn 1024 709%nat then Z.of_nat 709%nat else 1%Z) * ((if zz_in_Pn 1024 710%nat then Z.of_nat 710%nat else 1%Z) * ((if zz_in_Pn 1024 711%nat then Z.of_nat 711%nat else 1%Z) * ((if zz_in_Pn 1024 712%nat then Z.of_nat 712%nat else 1%Z) * ((if zz_in_Pn 1024 713%nat then Z.of_nat 713%nat else 1%Z) * ((if zz_in_Pn 1024 714%nat then Z.of_nat 714%nat else 1%Z) * ((if zz_in_Pn 1024 715%nat then Z.of_nat 715%nat else 1%Z) * ((if zz_in_Pn 1024 716%nat then Z.of_nat 716%nat else 1%Z) * ((if zz_in_Pn 1024 717%nat then Z.of_nat 717%nat else 1%Z) * ((if zz_in_Pn 1024 718%nat then Z.of_nat 718%nat else 1%Z) * ((if zz_in_Pn 1024 719%nat then Z.of_nat 719%nat else 1%Z) * (if zz_in_Pn 1024 720%nat then Z.of_nat 720%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_720.
    rewrite piu_zz_inPn_1024_719.
    rewrite piu_zz_inPn_1024_718.
    rewrite piu_zz_inPn_1024_717.
    rewrite piu_zz_inPn_1024_716.
    rewrite piu_zz_inPn_1024_715.
    rewrite piu_zz_inPn_1024_714.
    rewrite piu_zz_inPn_1024_713.
    rewrite piu_zz_inPn_1024_712.
    rewrite piu_zz_inPn_1024_711.
    rewrite piu_zz_inPn_1024_710.
    rewrite piu_zz_inPn_1024_709.
    rewrite piu_zz_inPn_1024_708.
    rewrite piu_zz_inPn_1024_707.
    rewrite piu_zz_inPn_1024_706.
    rewrite piu_zz_inPn_1024_705.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2783-L2803 (assert Hb84) *)
Lemma piu_zz_hb_1024_84 : piu_zz_zprod_seg 1024%nat (512%nat + 176%nat) 16%nat = ((if zz_in_Pn 1024 689%nat then Z.of_nat 689%nat else 1%Z) * ((if zz_in_Pn 1024 690%nat then Z.of_nat 690%nat else 1%Z) * ((if zz_in_Pn 1024 691%nat then Z.of_nat 691%nat else 1%Z) * ((if zz_in_Pn 1024 692%nat then Z.of_nat 692%nat else 1%Z) * ((if zz_in_Pn 1024 693%nat then Z.of_nat 693%nat else 1%Z) * ((if zz_in_Pn 1024 694%nat then Z.of_nat 694%nat else 1%Z) * ((if zz_in_Pn 1024 695%nat then Z.of_nat 695%nat else 1%Z) * ((if zz_in_Pn 1024 696%nat then Z.of_nat 696%nat else 1%Z) * ((if zz_in_Pn 1024 697%nat then Z.of_nat 697%nat else 1%Z) * ((if zz_in_Pn 1024 698%nat then Z.of_nat 698%nat else 1%Z) * ((if zz_in_Pn 1024 699%nat then Z.of_nat 699%nat else 1%Z) * ((if zz_in_Pn 1024 700%nat then Z.of_nat 700%nat else 1%Z) * ((if zz_in_Pn 1024 701%nat then Z.of_nat 701%nat else 1%Z) * ((if zz_in_Pn 1024 702%nat then Z.of_nat 702%nat else 1%Z) * ((if zz_in_Pn 1024 703%nat then Z.of_nat 703%nat else 1%Z) * (if zz_in_Pn 1024 704%nat then Z.of_nat 704%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_704.
    rewrite piu_zz_inPn_1024_703.
    rewrite piu_zz_inPn_1024_702.
    rewrite piu_zz_inPn_1024_701.
    rewrite piu_zz_inPn_1024_700.
    rewrite piu_zz_inPn_1024_699.
    rewrite piu_zz_inPn_1024_698.
    rewrite piu_zz_inPn_1024_697.
    rewrite piu_zz_inPn_1024_696.
    rewrite piu_zz_inPn_1024_695.
    rewrite piu_zz_inPn_1024_694.
    rewrite piu_zz_inPn_1024_693.
    rewrite piu_zz_inPn_1024_692.
    rewrite piu_zz_inPn_1024_691.
    rewrite piu_zz_inPn_1024_690.
    rewrite piu_zz_inPn_1024_689.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2804-L2824 (assert Hb85) *)
Lemma piu_zz_hb_1024_85 : piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) 16%nat = ((if zz_in_Pn 1024 673%nat then Z.of_nat 673%nat else 1%Z) * ((if zz_in_Pn 1024 674%nat then Z.of_nat 674%nat else 1%Z) * ((if zz_in_Pn 1024 675%nat then Z.of_nat 675%nat else 1%Z) * ((if zz_in_Pn 1024 676%nat then Z.of_nat 676%nat else 1%Z) * ((if zz_in_Pn 1024 677%nat then Z.of_nat 677%nat else 1%Z) * ((if zz_in_Pn 1024 678%nat then Z.of_nat 678%nat else 1%Z) * ((if zz_in_Pn 1024 679%nat then Z.of_nat 679%nat else 1%Z) * ((if zz_in_Pn 1024 680%nat then Z.of_nat 680%nat else 1%Z) * ((if zz_in_Pn 1024 681%nat then Z.of_nat 681%nat else 1%Z) * ((if zz_in_Pn 1024 682%nat then Z.of_nat 682%nat else 1%Z) * ((if zz_in_Pn 1024 683%nat then Z.of_nat 683%nat else 1%Z) * ((if zz_in_Pn 1024 684%nat then Z.of_nat 684%nat else 1%Z) * ((if zz_in_Pn 1024 685%nat then Z.of_nat 685%nat else 1%Z) * ((if zz_in_Pn 1024 686%nat then Z.of_nat 686%nat else 1%Z) * ((if zz_in_Pn 1024 687%nat then Z.of_nat 687%nat else 1%Z) * (if zz_in_Pn 1024 688%nat then Z.of_nat 688%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_688.
    rewrite piu_zz_inPn_1024_687.
    rewrite piu_zz_inPn_1024_686.
    rewrite piu_zz_inPn_1024_685.
    rewrite piu_zz_inPn_1024_684.
    rewrite piu_zz_inPn_1024_683.
    rewrite piu_zz_inPn_1024_682.
    rewrite piu_zz_inPn_1024_681.
    rewrite piu_zz_inPn_1024_680.
    rewrite piu_zz_inPn_1024_679.
    rewrite piu_zz_inPn_1024_678.
    rewrite piu_zz_inPn_1024_677.
    rewrite piu_zz_inPn_1024_676.
    rewrite piu_zz_inPn_1024_675.
    rewrite piu_zz_inPn_1024_674.
    rewrite piu_zz_inPn_1024_673.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2825-L2845 (assert Hb86) *)
Lemma piu_zz_hb_1024_86 : piu_zz_zprod_seg 1024%nat (512%nat + 144%nat) 16%nat = ((if zz_in_Pn 1024 657%nat then Z.of_nat 657%nat else 1%Z) * ((if zz_in_Pn 1024 658%nat then Z.of_nat 658%nat else 1%Z) * ((if zz_in_Pn 1024 659%nat then Z.of_nat 659%nat else 1%Z) * ((if zz_in_Pn 1024 660%nat then Z.of_nat 660%nat else 1%Z) * ((if zz_in_Pn 1024 661%nat then Z.of_nat 661%nat else 1%Z) * ((if zz_in_Pn 1024 662%nat then Z.of_nat 662%nat else 1%Z) * ((if zz_in_Pn 1024 663%nat then Z.of_nat 663%nat else 1%Z) * ((if zz_in_Pn 1024 664%nat then Z.of_nat 664%nat else 1%Z) * ((if zz_in_Pn 1024 665%nat then Z.of_nat 665%nat else 1%Z) * ((if zz_in_Pn 1024 666%nat then Z.of_nat 666%nat else 1%Z) * ((if zz_in_Pn 1024 667%nat then Z.of_nat 667%nat else 1%Z) * ((if zz_in_Pn 1024 668%nat then Z.of_nat 668%nat else 1%Z) * ((if zz_in_Pn 1024 669%nat then Z.of_nat 669%nat else 1%Z) * ((if zz_in_Pn 1024 670%nat then Z.of_nat 670%nat else 1%Z) * ((if zz_in_Pn 1024 671%nat then Z.of_nat 671%nat else 1%Z) * (if zz_in_Pn 1024 672%nat then Z.of_nat 672%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_672.
    rewrite piu_zz_inPn_1024_671.
    rewrite piu_zz_inPn_1024_670.
    rewrite piu_zz_inPn_1024_669.
    rewrite piu_zz_inPn_1024_668.
    rewrite piu_zz_inPn_1024_667.
    rewrite piu_zz_inPn_1024_666.
    rewrite piu_zz_inPn_1024_665.
    rewrite piu_zz_inPn_1024_664.
    rewrite piu_zz_inPn_1024_663.
    rewrite piu_zz_inPn_1024_662.
    rewrite piu_zz_inPn_1024_661.
    rewrite piu_zz_inPn_1024_660.
    rewrite piu_zz_inPn_1024_659.
    rewrite piu_zz_inPn_1024_658.
    rewrite piu_zz_inPn_1024_657.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2846-L2866 (assert Hb87) *)
Lemma piu_zz_hb_1024_87 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 16%nat = ((if zz_in_Pn 1024 641%nat then Z.of_nat 641%nat else 1%Z) * ((if zz_in_Pn 1024 642%nat then Z.of_nat 642%nat else 1%Z) * ((if zz_in_Pn 1024 643%nat then Z.of_nat 643%nat else 1%Z) * ((if zz_in_Pn 1024 644%nat then Z.of_nat 644%nat else 1%Z) * ((if zz_in_Pn 1024 645%nat then Z.of_nat 645%nat else 1%Z) * ((if zz_in_Pn 1024 646%nat then Z.of_nat 646%nat else 1%Z) * ((if zz_in_Pn 1024 647%nat then Z.of_nat 647%nat else 1%Z) * ((if zz_in_Pn 1024 648%nat then Z.of_nat 648%nat else 1%Z) * ((if zz_in_Pn 1024 649%nat then Z.of_nat 649%nat else 1%Z) * ((if zz_in_Pn 1024 650%nat then Z.of_nat 650%nat else 1%Z) * ((if zz_in_Pn 1024 651%nat then Z.of_nat 651%nat else 1%Z) * ((if zz_in_Pn 1024 652%nat then Z.of_nat 652%nat else 1%Z) * ((if zz_in_Pn 1024 653%nat then Z.of_nat 653%nat else 1%Z) * ((if zz_in_Pn 1024 654%nat then Z.of_nat 654%nat else 1%Z) * ((if zz_in_Pn 1024 655%nat then Z.of_nat 655%nat else 1%Z) * (if zz_in_Pn 1024 656%nat then Z.of_nat 656%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_656.
    rewrite piu_zz_inPn_1024_655.
    rewrite piu_zz_inPn_1024_654.
    rewrite piu_zz_inPn_1024_653.
    rewrite piu_zz_inPn_1024_652.
    rewrite piu_zz_inPn_1024_651.
    rewrite piu_zz_inPn_1024_650.
    rewrite piu_zz_inPn_1024_649.
    rewrite piu_zz_inPn_1024_648.
    rewrite piu_zz_inPn_1024_647.
    rewrite piu_zz_inPn_1024_646.
    rewrite piu_zz_inPn_1024_645.
    rewrite piu_zz_inPn_1024_644.
    rewrite piu_zz_inPn_1024_643.
    rewrite piu_zz_inPn_1024_642.
    rewrite piu_zz_inPn_1024_641.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2867-L2887 (assert Hb88) *)
Lemma piu_zz_hb_1024_88 : piu_zz_zprod_seg 1024%nat (512%nat + 112%nat) 16%nat = ((if zz_in_Pn 1024 625%nat then Z.of_nat 625%nat else 1%Z) * ((if zz_in_Pn 1024 626%nat then Z.of_nat 626%nat else 1%Z) * ((if zz_in_Pn 1024 627%nat then Z.of_nat 627%nat else 1%Z) * ((if zz_in_Pn 1024 628%nat then Z.of_nat 628%nat else 1%Z) * ((if zz_in_Pn 1024 629%nat then Z.of_nat 629%nat else 1%Z) * ((if zz_in_Pn 1024 630%nat then Z.of_nat 630%nat else 1%Z) * ((if zz_in_Pn 1024 631%nat then Z.of_nat 631%nat else 1%Z) * ((if zz_in_Pn 1024 632%nat then Z.of_nat 632%nat else 1%Z) * ((if zz_in_Pn 1024 633%nat then Z.of_nat 633%nat else 1%Z) * ((if zz_in_Pn 1024 634%nat then Z.of_nat 634%nat else 1%Z) * ((if zz_in_Pn 1024 635%nat then Z.of_nat 635%nat else 1%Z) * ((if zz_in_Pn 1024 636%nat then Z.of_nat 636%nat else 1%Z) * ((if zz_in_Pn 1024 637%nat then Z.of_nat 637%nat else 1%Z) * ((if zz_in_Pn 1024 638%nat then Z.of_nat 638%nat else 1%Z) * ((if zz_in_Pn 1024 639%nat then Z.of_nat 639%nat else 1%Z) * (if zz_in_Pn 1024 640%nat then Z.of_nat 640%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_640.
    rewrite piu_zz_inPn_1024_639.
    rewrite piu_zz_inPn_1024_638.
    rewrite piu_zz_inPn_1024_637.
    rewrite piu_zz_inPn_1024_636.
    rewrite piu_zz_inPn_1024_635.
    rewrite piu_zz_inPn_1024_634.
    rewrite piu_zz_inPn_1024_633.
    rewrite piu_zz_inPn_1024_632.
    rewrite piu_zz_inPn_1024_631.
    rewrite piu_zz_inPn_1024_630.
    rewrite piu_zz_inPn_1024_629.
    rewrite piu_zz_inPn_1024_628.
    rewrite piu_zz_inPn_1024_627.
    rewrite piu_zz_inPn_1024_626.
    rewrite piu_zz_inPn_1024_625.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2888-L2908 (assert Hb89) *)
Lemma piu_zz_hb_1024_89 : piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) 16%nat = ((if zz_in_Pn 1024 609%nat then Z.of_nat 609%nat else 1%Z) * ((if zz_in_Pn 1024 610%nat then Z.of_nat 610%nat else 1%Z) * ((if zz_in_Pn 1024 611%nat then Z.of_nat 611%nat else 1%Z) * ((if zz_in_Pn 1024 612%nat then Z.of_nat 612%nat else 1%Z) * ((if zz_in_Pn 1024 613%nat then Z.of_nat 613%nat else 1%Z) * ((if zz_in_Pn 1024 614%nat then Z.of_nat 614%nat else 1%Z) * ((if zz_in_Pn 1024 615%nat then Z.of_nat 615%nat else 1%Z) * ((if zz_in_Pn 1024 616%nat then Z.of_nat 616%nat else 1%Z) * ((if zz_in_Pn 1024 617%nat then Z.of_nat 617%nat else 1%Z) * ((if zz_in_Pn 1024 618%nat then Z.of_nat 618%nat else 1%Z) * ((if zz_in_Pn 1024 619%nat then Z.of_nat 619%nat else 1%Z) * ((if zz_in_Pn 1024 620%nat then Z.of_nat 620%nat else 1%Z) * ((if zz_in_Pn 1024 621%nat then Z.of_nat 621%nat else 1%Z) * ((if zz_in_Pn 1024 622%nat then Z.of_nat 622%nat else 1%Z) * ((if zz_in_Pn 1024 623%nat then Z.of_nat 623%nat else 1%Z) * (if zz_in_Pn 1024 624%nat then Z.of_nat 624%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_624.
    rewrite piu_zz_inPn_1024_623.
    rewrite piu_zz_inPn_1024_622.
    rewrite piu_zz_inPn_1024_621.
    rewrite piu_zz_inPn_1024_620.
    rewrite piu_zz_inPn_1024_619.
    rewrite piu_zz_inPn_1024_618.
    rewrite piu_zz_inPn_1024_617.
    rewrite piu_zz_inPn_1024_616.
    rewrite piu_zz_inPn_1024_615.
    rewrite piu_zz_inPn_1024_614.
    rewrite piu_zz_inPn_1024_613.
    rewrite piu_zz_inPn_1024_612.
    rewrite piu_zz_inPn_1024_611.
    rewrite piu_zz_inPn_1024_610.
    rewrite piu_zz_inPn_1024_609.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2909-L2929 (assert Hb90) *)
Lemma piu_zz_hb_1024_90 : piu_zz_zprod_seg 1024%nat (512%nat + 80%nat) 16%nat = ((if zz_in_Pn 1024 593%nat then Z.of_nat 593%nat else 1%Z) * ((if zz_in_Pn 1024 594%nat then Z.of_nat 594%nat else 1%Z) * ((if zz_in_Pn 1024 595%nat then Z.of_nat 595%nat else 1%Z) * ((if zz_in_Pn 1024 596%nat then Z.of_nat 596%nat else 1%Z) * ((if zz_in_Pn 1024 597%nat then Z.of_nat 597%nat else 1%Z) * ((if zz_in_Pn 1024 598%nat then Z.of_nat 598%nat else 1%Z) * ((if zz_in_Pn 1024 599%nat then Z.of_nat 599%nat else 1%Z) * ((if zz_in_Pn 1024 600%nat then Z.of_nat 600%nat else 1%Z) * ((if zz_in_Pn 1024 601%nat then Z.of_nat 601%nat else 1%Z) * ((if zz_in_Pn 1024 602%nat then Z.of_nat 602%nat else 1%Z) * ((if zz_in_Pn 1024 603%nat then Z.of_nat 603%nat else 1%Z) * ((if zz_in_Pn 1024 604%nat then Z.of_nat 604%nat else 1%Z) * ((if zz_in_Pn 1024 605%nat then Z.of_nat 605%nat else 1%Z) * ((if zz_in_Pn 1024 606%nat then Z.of_nat 606%nat else 1%Z) * ((if zz_in_Pn 1024 607%nat then Z.of_nat 607%nat else 1%Z) * (if zz_in_Pn 1024 608%nat then Z.of_nat 608%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_608.
    rewrite piu_zz_inPn_1024_607.
    rewrite piu_zz_inPn_1024_606.
    rewrite piu_zz_inPn_1024_605.
    rewrite piu_zz_inPn_1024_604.
    rewrite piu_zz_inPn_1024_603.
    rewrite piu_zz_inPn_1024_602.
    rewrite piu_zz_inPn_1024_601.
    rewrite piu_zz_inPn_1024_600.
    rewrite piu_zz_inPn_1024_599.
    rewrite piu_zz_inPn_1024_598.
    rewrite piu_zz_inPn_1024_597.
    rewrite piu_zz_inPn_1024_596.
    rewrite piu_zz_inPn_1024_595.
    rewrite piu_zz_inPn_1024_594.
    rewrite piu_zz_inPn_1024_593.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2930-L2950 (assert Hb91) *)
Lemma piu_zz_hb_1024_91 : piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 16%nat = ((if zz_in_Pn 1024 577%nat then Z.of_nat 577%nat else 1%Z) * ((if zz_in_Pn 1024 578%nat then Z.of_nat 578%nat else 1%Z) * ((if zz_in_Pn 1024 579%nat then Z.of_nat 579%nat else 1%Z) * ((if zz_in_Pn 1024 580%nat then Z.of_nat 580%nat else 1%Z) * ((if zz_in_Pn 1024 581%nat then Z.of_nat 581%nat else 1%Z) * ((if zz_in_Pn 1024 582%nat then Z.of_nat 582%nat else 1%Z) * ((if zz_in_Pn 1024 583%nat then Z.of_nat 583%nat else 1%Z) * ((if zz_in_Pn 1024 584%nat then Z.of_nat 584%nat else 1%Z) * ((if zz_in_Pn 1024 585%nat then Z.of_nat 585%nat else 1%Z) * ((if zz_in_Pn 1024 586%nat then Z.of_nat 586%nat else 1%Z) * ((if zz_in_Pn 1024 587%nat then Z.of_nat 587%nat else 1%Z) * ((if zz_in_Pn 1024 588%nat then Z.of_nat 588%nat else 1%Z) * ((if zz_in_Pn 1024 589%nat then Z.of_nat 589%nat else 1%Z) * ((if zz_in_Pn 1024 590%nat then Z.of_nat 590%nat else 1%Z) * ((if zz_in_Pn 1024 591%nat then Z.of_nat 591%nat else 1%Z) * (if zz_in_Pn 1024 592%nat then Z.of_nat 592%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_592.
    rewrite piu_zz_inPn_1024_591.
    rewrite piu_zz_inPn_1024_590.
    rewrite piu_zz_inPn_1024_589.
    rewrite piu_zz_inPn_1024_588.
    rewrite piu_zz_inPn_1024_587.
    rewrite piu_zz_inPn_1024_586.
    rewrite piu_zz_inPn_1024_585.
    rewrite piu_zz_inPn_1024_584.
    rewrite piu_zz_inPn_1024_583.
    rewrite piu_zz_inPn_1024_582.
    rewrite piu_zz_inPn_1024_581.
    rewrite piu_zz_inPn_1024_580.
    rewrite piu_zz_inPn_1024_579.
    rewrite piu_zz_inPn_1024_578.
    rewrite piu_zz_inPn_1024_577.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2951-L2971 (assert Hb92) *)
Lemma piu_zz_hb_1024_92 : piu_zz_zprod_seg 1024%nat (512%nat + 48%nat) 16%nat = ((if zz_in_Pn 1024 561%nat then Z.of_nat 561%nat else 1%Z) * ((if zz_in_Pn 1024 562%nat then Z.of_nat 562%nat else 1%Z) * ((if zz_in_Pn 1024 563%nat then Z.of_nat 563%nat else 1%Z) * ((if zz_in_Pn 1024 564%nat then Z.of_nat 564%nat else 1%Z) * ((if zz_in_Pn 1024 565%nat then Z.of_nat 565%nat else 1%Z) * ((if zz_in_Pn 1024 566%nat then Z.of_nat 566%nat else 1%Z) * ((if zz_in_Pn 1024 567%nat then Z.of_nat 567%nat else 1%Z) * ((if zz_in_Pn 1024 568%nat then Z.of_nat 568%nat else 1%Z) * ((if zz_in_Pn 1024 569%nat then Z.of_nat 569%nat else 1%Z) * ((if zz_in_Pn 1024 570%nat then Z.of_nat 570%nat else 1%Z) * ((if zz_in_Pn 1024 571%nat then Z.of_nat 571%nat else 1%Z) * ((if zz_in_Pn 1024 572%nat then Z.of_nat 572%nat else 1%Z) * ((if zz_in_Pn 1024 573%nat then Z.of_nat 573%nat else 1%Z) * ((if zz_in_Pn 1024 574%nat then Z.of_nat 574%nat else 1%Z) * ((if zz_in_Pn 1024 575%nat then Z.of_nat 575%nat else 1%Z) * (if zz_in_Pn 1024 576%nat then Z.of_nat 576%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_576.
    rewrite piu_zz_inPn_1024_575.
    rewrite piu_zz_inPn_1024_574.
    rewrite piu_zz_inPn_1024_573.
    rewrite piu_zz_inPn_1024_572.
    rewrite piu_zz_inPn_1024_571.
    rewrite piu_zz_inPn_1024_570.
    rewrite piu_zz_inPn_1024_569.
    rewrite piu_zz_inPn_1024_568.
    rewrite piu_zz_inPn_1024_567.
    rewrite piu_zz_inPn_1024_566.
    rewrite piu_zz_inPn_1024_565.
    rewrite piu_zz_inPn_1024_564.
    rewrite piu_zz_inPn_1024_563.
    rewrite piu_zz_inPn_1024_562.
    rewrite piu_zz_inPn_1024_561.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2972-L2992 (assert Hb93) *)
Lemma piu_zz_hb_1024_93 : piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) 16%nat = ((if zz_in_Pn 1024 545%nat then Z.of_nat 545%nat else 1%Z) * ((if zz_in_Pn 1024 546%nat then Z.of_nat 546%nat else 1%Z) * ((if zz_in_Pn 1024 547%nat then Z.of_nat 547%nat else 1%Z) * ((if zz_in_Pn 1024 548%nat then Z.of_nat 548%nat else 1%Z) * ((if zz_in_Pn 1024 549%nat then Z.of_nat 549%nat else 1%Z) * ((if zz_in_Pn 1024 550%nat then Z.of_nat 550%nat else 1%Z) * ((if zz_in_Pn 1024 551%nat then Z.of_nat 551%nat else 1%Z) * ((if zz_in_Pn 1024 552%nat then Z.of_nat 552%nat else 1%Z) * ((if zz_in_Pn 1024 553%nat then Z.of_nat 553%nat else 1%Z) * ((if zz_in_Pn 1024 554%nat then Z.of_nat 554%nat else 1%Z) * ((if zz_in_Pn 1024 555%nat then Z.of_nat 555%nat else 1%Z) * ((if zz_in_Pn 1024 556%nat then Z.of_nat 556%nat else 1%Z) * ((if zz_in_Pn 1024 557%nat then Z.of_nat 557%nat else 1%Z) * ((if zz_in_Pn 1024 558%nat then Z.of_nat 558%nat else 1%Z) * ((if zz_in_Pn 1024 559%nat then Z.of_nat 559%nat else 1%Z) * (if zz_in_Pn 1024 560%nat then Z.of_nat 560%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_560.
    rewrite piu_zz_inPn_1024_559.
    rewrite piu_zz_inPn_1024_558.
    rewrite piu_zz_inPn_1024_557.
    rewrite piu_zz_inPn_1024_556.
    rewrite piu_zz_inPn_1024_555.
    rewrite piu_zz_inPn_1024_554.
    rewrite piu_zz_inPn_1024_553.
    rewrite piu_zz_inPn_1024_552.
    rewrite piu_zz_inPn_1024_551.
    rewrite piu_zz_inPn_1024_550.
    rewrite piu_zz_inPn_1024_549.
    rewrite piu_zz_inPn_1024_548.
    rewrite piu_zz_inPn_1024_547.
    rewrite piu_zz_inPn_1024_546.
    rewrite piu_zz_inPn_1024_545.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2993-L3013 (assert Hb94) *)
Lemma piu_zz_hb_1024_94 : piu_zz_zprod_seg 1024%nat (512%nat + 16%nat) 16%nat = ((if zz_in_Pn 1024 529%nat then Z.of_nat 529%nat else 1%Z) * ((if zz_in_Pn 1024 530%nat then Z.of_nat 530%nat else 1%Z) * ((if zz_in_Pn 1024 531%nat then Z.of_nat 531%nat else 1%Z) * ((if zz_in_Pn 1024 532%nat then Z.of_nat 532%nat else 1%Z) * ((if zz_in_Pn 1024 533%nat then Z.of_nat 533%nat else 1%Z) * ((if zz_in_Pn 1024 534%nat then Z.of_nat 534%nat else 1%Z) * ((if zz_in_Pn 1024 535%nat then Z.of_nat 535%nat else 1%Z) * ((if zz_in_Pn 1024 536%nat then Z.of_nat 536%nat else 1%Z) * ((if zz_in_Pn 1024 537%nat then Z.of_nat 537%nat else 1%Z) * ((if zz_in_Pn 1024 538%nat then Z.of_nat 538%nat else 1%Z) * ((if zz_in_Pn 1024 539%nat then Z.of_nat 539%nat else 1%Z) * ((if zz_in_Pn 1024 540%nat then Z.of_nat 540%nat else 1%Z) * ((if zz_in_Pn 1024 541%nat then Z.of_nat 541%nat else 1%Z) * ((if zz_in_Pn 1024 542%nat then Z.of_nat 542%nat else 1%Z) * ((if zz_in_Pn 1024 543%nat then Z.of_nat 543%nat else 1%Z) * (if zz_in_Pn 1024 544%nat then Z.of_nat 544%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_544.
    rewrite piu_zz_inPn_1024_543.
    rewrite piu_zz_inPn_1024_542.
    rewrite piu_zz_inPn_1024_541.
    rewrite piu_zz_inPn_1024_540.
    rewrite piu_zz_inPn_1024_539.
    rewrite piu_zz_inPn_1024_538.
    rewrite piu_zz_inPn_1024_537.
    rewrite piu_zz_inPn_1024_536.
    rewrite piu_zz_inPn_1024_535.
    rewrite piu_zz_inPn_1024_534.
    rewrite piu_zz_inPn_1024_533.
    rewrite piu_zz_inPn_1024_532.
    rewrite piu_zz_inPn_1024_531.
    rewrite piu_zz_inPn_1024_530.
    rewrite piu_zz_inPn_1024_529.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L3014-L3034 (assert Hb95) *)
Lemma piu_zz_hb_1024_95 : piu_zz_zprod_seg 1024%nat 512%nat 16%nat = ((if zz_in_Pn 1024 513%nat then Z.of_nat 513%nat else 1%Z) * ((if zz_in_Pn 1024 514%nat then Z.of_nat 514%nat else 1%Z) * ((if zz_in_Pn 1024 515%nat then Z.of_nat 515%nat else 1%Z) * ((if zz_in_Pn 1024 516%nat then Z.of_nat 516%nat else 1%Z) * ((if zz_in_Pn 1024 517%nat then Z.of_nat 517%nat else 1%Z) * ((if zz_in_Pn 1024 518%nat then Z.of_nat 518%nat else 1%Z) * ((if zz_in_Pn 1024 519%nat then Z.of_nat 519%nat else 1%Z) * ((if zz_in_Pn 1024 520%nat then Z.of_nat 520%nat else 1%Z) * ((if zz_in_Pn 1024 521%nat then Z.of_nat 521%nat else 1%Z) * ((if zz_in_Pn 1024 522%nat then Z.of_nat 522%nat else 1%Z) * ((if zz_in_Pn 1024 523%nat then Z.of_nat 523%nat else 1%Z) * ((if zz_in_Pn 1024 524%nat then Z.of_nat 524%nat else 1%Z) * ((if zz_in_Pn 1024 525%nat then Z.of_nat 525%nat else 1%Z) * ((if zz_in_Pn 1024 526%nat then Z.of_nat 526%nat else 1%Z) * ((if zz_in_Pn 1024 527%nat then Z.of_nat 527%nat else 1%Z) * (if zz_in_Pn 1024 528%nat then Z.of_nat 528%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_528.
    rewrite piu_zz_inPn_1024_527.
    rewrite piu_zz_inPn_1024_526.
    rewrite piu_zz_inPn_1024_525.
    rewrite piu_zz_inPn_1024_524.
    rewrite piu_zz_inPn_1024_523.
    rewrite piu_zz_inPn_1024_522.
    rewrite piu_zz_inPn_1024_521.
    rewrite piu_zz_inPn_1024_520.
    rewrite piu_zz_inPn_1024_519.
    rewrite piu_zz_inPn_1024_518.
    rewrite piu_zz_inPn_1024_517.
    rewrite piu_zz_inPn_1024_516.
    rewrite piu_zz_inPn_1024_515.
    rewrite piu_zz_inPn_1024_514.
    rewrite piu_zz_inPn_1024_513.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
