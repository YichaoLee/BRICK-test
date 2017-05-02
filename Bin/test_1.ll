; ModuleID = 'test_1.bc'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 0, i32* %retval
  call void @llvm.dbg.declare(metadata !{i32* %x}, metadata !12), !dbg !14
  call void @llvm.dbg.declare(metadata !{i32* %y}, metadata !15), !dbg !16
  call void @llvm.dbg.declare(metadata !{i32* %z}, metadata !17), !dbg !18
  %0 = load i32* %y, align 4, !dbg !19
  %conv = zext i32 %0 to i64, !dbg !19
  %sub = sub nsw i64 %conv, 100000000000, !dbg !19
  %conv1 = trunc i64 %sub to i32, !dbg !19
  store i32 %conv1, i32* %x, align 4, !dbg !19
  %1 = load i32* %y, align 4, !dbg !20
  %cmp = icmp ugt i32 %1, 1, !dbg !20
  br i1 %cmp, label %if.then, label %if.else, !dbg !20

if.then:                                          ; preds = %entry
  %2 = load i32* %x, align 4, !dbg !22
  %3 = load i32* %y, align 4, !dbg !22
  %div = udiv i32 %2, %3, !dbg !22
  store i32 %div, i32* %z, align 4, !dbg !22
  br label %if.end13, !dbg !22

if.else:                                          ; preds = %entry
  %4 = load i32* %y, align 4, !dbg !23
  %cmp3 = icmp uge i32 %4, -1, !dbg !23
  br i1 %cmp3, label %if.then5, label %if.else8, !dbg !23

if.then5:                                         ; preds = %if.else
  %5 = load i32* %y, align 4, !dbg !25
  %conv6 = uitofp i32 %5 to double, !dbg !25
  %call = call double @asin(double %conv6) #3, !dbg !25
  %conv7 = fptoui double %call to i32, !dbg !25
  store i32 %conv7, i32* %z, align 4, !dbg !25
  br label %if.end, !dbg !25

if.else8:                                         ; preds = %if.else
  %6 = load i32* %y, align 4, !dbg !26
  %sub9 = sub i32 0, %6, !dbg !26
  %conv10 = uitofp i32 %sub9 to double, !dbg !26
  %call11 = call double @sqrt(double %conv10) #3, !dbg !26
  %conv12 = fptoui double %call11 to i32, !dbg !26
  store i32 %conv12, i32* %z, align 4, !dbg !26
  br label %if.end

if.end:                                           ; preds = %if.else8, %if.then5
  br label %if.end13

if.end13:                                         ; preds = %if.end, %if.then
  ret i32 0, !dbg !27
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata) #1

; Function Attrs: nounwind
declare double @asin(double) #2

; Function Attrs: nounwind
declare double @sqrt(double) #2

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { nounwind "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!9, !10}
!llvm.ident = !{!11}

!0 = metadata !{i32 786449, metadata !1, i32 12, metadata !"clang version 3.5.2 (tags/RELEASE_352/final)", i1 false, metadata !"", i32 0, metadata !2, metadata !2, metadata !3, metadata !2, metadata !2, metadata !"", i32 1} ; [ DW_TAG_compile_unit ] [/home/lich/Documents/Link to BRICK-tool/Bin/test_1.c] [DW_LANG_C99]
!1 = metadata !{metadata !"test_1.c", metadata !"/home/lich/Documents/Link to BRICK-tool/Bin"}
!2 = metadata !{}
!3 = metadata !{metadata !4}
!4 = metadata !{i32 786478, metadata !1, metadata !5, metadata !"main", metadata !"main", metadata !"", i32 4, metadata !6, i1 false, i1 true, i32 0, i32 0, null, i32 0, i1 false, i32 ()* @main, null, null, metadata !2, i32 4} ; [ DW_TAG_subprogram ] [line 4] [def] [main]
!5 = metadata !{i32 786473, metadata !1}          ; [ DW_TAG_file_type ] [/home/lich/Documents/Link to BRICK-tool/Bin/test_1.c]
!6 = metadata !{i32 786453, i32 0, null, metadata !"", i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !7, i32 0, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!7 = metadata !{metadata !8}
!8 = metadata !{i32 786468, null, null, metadata !"int", i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ] [int] [line 0, size 32, align 32, offset 0, enc DW_ATE_signed]
!9 = metadata !{i32 2, metadata !"Dwarf Version", i32 4}
!10 = metadata !{i32 2, metadata !"Debug Info Version", i32 1}
!11 = metadata !{metadata !"clang version 3.5.2 (tags/RELEASE_352/final)"}
!12 = metadata !{i32 786688, metadata !4, metadata !"x", metadata !5, i32 5, metadata !13, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [x] [line 5]
!13 = metadata !{i32 786468, null, null, metadata !"unsigned int", i32 0, i64 32, i64 32, i64 0, i32 0, i32 7} ; [ DW_TAG_base_type ] [unsigned int] [line 0, size 32, align 32, offset 0, enc DW_ATE_unsigned]
!14 = metadata !{i32 5, i32 11, metadata !4, null}
!15 = metadata !{i32 786688, metadata !4, metadata !"y", metadata !5, i32 5, metadata !13, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [y] [line 5]
!16 = metadata !{i32 5, i32 13, metadata !4, null}
!17 = metadata !{i32 786688, metadata !4, metadata !"z", metadata !5, i32 5, metadata !13, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [z] [line 5]
!18 = metadata !{i32 5, i32 15, metadata !4, null}
!19 = metadata !{i32 6, i32 2, metadata !4, null}
!20 = metadata !{i32 7, i32 5, metadata !21, null}
!21 = metadata !{i32 786443, metadata !1, metadata !4, i32 7, i32 5, i32 0, i32 0} ; [ DW_TAG_lexical_block ] [/home/lich/Documents/Link to BRICK-tool/Bin/test_1.c]
!22 = metadata !{i32 8, i32 3, metadata !21, null} ; [ DW_TAG_imported_declaration ]
!23 = metadata !{i32 9, i32 10, metadata !24, null}
!24 = metadata !{i32 786443, metadata !1, metadata !21, i32 9, i32 10, i32 0, i32 1} ; [ DW_TAG_lexical_block ] [/home/lich/Documents/Link to BRICK-tool/Bin/test_1.c]
!25 = metadata !{i32 10, i32 5, metadata !24, null}
!26 = metadata !{i32 12, i32 5, metadata !24, null}
!27 = metadata !{i32 13, i32 2, metadata !4, null}
