; ModuleID = '/home/guswjd/sp/realdef/build/r2.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.libraw_decoder_info_t.972 = type { ptr, i32 }
%class.LibRaw = type { ptr, %struct.libraw_data_t, ptr, %struct.libraw_internal_data_t, [2048 x %struct.decode], ptr, ptr, [10 x %struct.tiff_ifd_t], %class.libraw_memmgr, %struct.libraw_callbacks_t, { i64, i64 }, { i64, i64 }, { i64, i64 }, ptr, ptr, ptr, i64, ptr, ptr, ptr, ptr }
%struct.libraw_data_t = type { ptr, %struct.libraw_image_sizes_t, %struct.libraw_iparams_t, %struct.libraw_lensinfo_t, %struct.libraw_makernotes_t, %struct.libraw_shootinginfo_t, %struct.libraw_output_params_t, %struct.libraw_raw_unpack_params_t, i32, i32, %struct.libraw_colordata_t, %struct.libraw_imgother_t, %struct.libraw_thumbnail_t, %struct.libraw_thumbnail_list_t, %struct.libraw_rawdata_t, ptr }
%struct.libraw_image_sizes_t = type { i16, i16, i16, i16, i16, i16, i16, i16, i32, double, i32, [8 x [4 x i32]], i16, [2 x %struct.libraw_raw_inset_crop_t] }
%struct.libraw_raw_inset_crop_t = type { i16, i16, i16, i16 }
%struct.libraw_iparams_t = type { [4 x i8], [64 x i8], [64 x i8], [64 x i8], [64 x i8], [64 x i8], i32, i32, i32, i32, i32, i32, [6 x [6 x i8]], [6 x [6 x i8]], [5 x i8], i32, ptr }
%struct.libraw_lensinfo_t = type { float, float, float, float, float, [128 x i8], [128 x i8], [128 x i8], [128 x i8], i16, %struct.libraw_nikonlens_t, %struct.libraw_dnglens_t, %struct.libraw_makernotes_lens_t }
%struct.libraw_nikonlens_t = type { float, i8, i8, i8, i8 }
%struct.libraw_dnglens_t = type { float, float, float, float }
%struct.libraw_makernotes_lens_t = type { i64, [128 x i8], i16, i16, i64, i16, i16, [64 x i8], i16, [16 x i8], [16 x i8], float, float, float, float, float, float, float, float, float, float, float, float, float, float, float, i64, [128 x i8], i64, [128 x i8], i64, [128 x i8], i16, float }
%struct.libraw_makernotes_t = type { %struct.libraw_canon_makernotes_t, %struct.libraw_nikon_makernotes_t, %struct.libraw_hasselblad_makernotes_t, %struct.libraw_fuji_info_t, %struct.libraw_olympus_makernotes_t, %struct.libraw_sony_info_t, %struct.libraw_kodak_makernotes_t, %struct.libraw_panasonic_makernotes_t, %struct.libraw_pentax_makernotes_t, %struct.libraw_p1_makernotes_t, %struct.libraw_ricoh_makernotes_t, %struct.libraw_samsung_makernotes_t, %struct.libraw_metadata_common_t }
%struct.libraw_canon_makernotes_t = type { i32, i32, i32, i32, [4 x i32], i32, [4 x i32], i16, i16, i8, i16, i16, i16, i16, i16, i16, i16, i16, i16, i16, i16, i16, i16, i32, float, i16, i16, i16, i32, i16, i32, i32, i16, i32, %struct.libraw_raw_inset_crop_t, %struct.libraw_raw_inset_crop_t, %struct.libraw_raw_inset_crop_t, %struct.libraw_raw_inset_crop_t, %struct.libraw_raw_inset_crop_t, [2 x i16] }
%struct.libraw_nikon_makernotes_t = type { double, i16, i16, [7 x i8], i8, i8, [13 x i8], [20 x i8], [4 x i8], [4 x i8], [4 x i8], i8, i8, i8, i8, i8, [2 x i8], i8, i8, i8, i8, i8, [4 x i8], [4 x i8], i8, i16, i32, i32, i32, i32, [4 x double], i8, i8, i8, i32, i32, i32, i8, [4 x i16], i16, %struct.libraw_raw_inset_crop_t, i16, i16, i16, i32, i16, double, double, double }
%struct.libraw_hasselblad_makernotes_t = type { i32, double, [8 x i8], [64 x i8], [64 x i8], i32, i32, i32, i32, [32 x i8], [64 x i8], i32, [2 x i32], [2 x i32], [4 x [3 x double]] }
%struct.libraw_fuji_info_t = type { float, i16, i16, i16, i16, i16, i16, i16, i16, float, i16, i16, [2 x i16], i16, i32, i32, i16, [3 x i16], i16, i16, i16, i16, i16, i32, i16, [13 x i8], [5 x i8], [5 x i8], i32, i16, i32, i16, [9 x i16], [32 x i32], i32, i32, i32, [2 x float], i32 }
%struct.libraw_olympus_makernotes_t = type { [6 x i8], i16, [2 x i32], [5 x i16], i16, [2 x i16], i16, i16, [64 x i32], [5 x double], i16, i8, [3 x i16], [3 x i32], i16, i16, i16, i16, double, [4 x i16], [2 x i32], i8, i32, i16, i16 }
%struct.libraw_sony_info_t = type { i16, i8, i8, i32, i8, i32, i8, i8, i16, [2 x i16], i8, i8, i16, [10 x i8], i8, i8, [4 x i16], i16, i8, i8, i8, i16, i32, i16, [2 x i16], i16, i16, i16, i16, i16, i16, i32, float, i16, i32, i32, i16, [20 x i8], i32, i16, i32, i8, i8, i16, i16, i16, i16, i16, i16, i16, i16, i16, i32, i16, [16 x i8] }
%struct.libraw_kodak_makernotes_t = type { i16, i16, i16, i16, i16, i16, [3 x [3 x float]], [3 x [3 x float]], [3 x [3 x float]], [3 x [3 x float]], [3 x [3 x float]], [3 x [3 x float]], i16, i16, i16, i16, float, float }
%struct.libraw_panasonic_makernotes_t = type { i16, i16, [8 x float], i32, float, [3 x i32], i16, i16, i32, i32 }
%struct.libraw_pentax_makernotes_t = type { [4 x i8], [2 x i16], [2 x i16], i16, i32, i32, i16, i16, i8, i8, i16 }
%struct.libraw_p1_makernotes_t = type { [64 x i8], [64 x i8], [256 x i8], [64 x i8] }
%struct.libraw_ricoh_makernotes_t = type { i16, [2 x i32], [2 x i32], i16, i32, i32, i32, i32, i16, i16, i16, i16, i16, i16, double, double }
%struct.libraw_samsung_makernotes_t = type { [4 x i32], [4 x i32], [2 x i32], [11 x i32], double, i32, [32 x i8] }
%struct.libraw_metadata_common_t = type { float, float, float, float, float, float, float, float, float, float, float, float, float, float, float, float, i16, [128 x i8], float, [4 x %struct.libraw_afinfo_item_t], i32 }
%struct.libraw_afinfo_item_t = type { i32, i16, i32, i32, ptr }
%struct.libraw_shootinginfo_t = type { i16, i16, i16, i16, i16, i16, i16, [64 x i8], [64 x i8] }
%struct.libraw_output_params_t = type { [4 x i32], [4 x i32], [4 x double], [6 x double], [4 x float], float, float, i32, i32, i32, i32, i32, i32, i32, ptr, ptr, ptr, ptr, i32, i32, i32, i32, i32, i32, [4 x i32], i32, i32, float, float, i32, i32, i32, i32, i32, i32, i32, float, float, i32, i32 }
%struct.libraw_raw_unpack_params_t = type { i32, i32, i32, i32, i32, i32, i32, float, [5 x i8], ptr }
%struct.libraw_colordata_t = type { [65536 x i16], [4104 x i32], i32, i32, i32, [4 x i64], float, float, [8 x [8 x i16]], [4 x float], [4 x float], [3 x [4 x float]], [3 x [4 x float]], [3 x [4 x float]], [4 x [3 x float]], %struct.ph1_t, float, float, [64 x i8], [64 x i8], [64 x i8], [64 x i8], [17 x i8], [64 x i8], ptr, i32, [8 x i32], [2 x %struct.libraw_dng_color_t], %struct.libraw_dng_levels_t, [256 x [4 x i32]], [64 x [5 x float]], i32, [2 x %struct.libraw_P1_color_t], i32, i32 }
%struct.ph1_t = type { i32, i32, i32, i32, i32, i32, i32, i32, float }
%struct.libraw_dng_color_t = type { i32, i16, [4 x [4 x float]], [4 x [3 x float]], [3 x [4 x float]] }
%struct.libraw_dng_levels_t = type { i32, [4104 x i32], i32, [4104 x float], float, [4 x i32], [4 x i16], [4 x float], i32, [4 x float], [4 x float], float, float }
%struct.libraw_P1_color_t = type { [9 x float] }
%struct.libraw_imgother_t = type { float, float, float, float, i64, i32, [32 x i32], %struct.libraw_gps_info_t, [512 x i8], [64 x i8], [4 x float] }
%struct.libraw_gps_info_t = type { [3 x float], [3 x float], [3 x float], float, i8, i8, i8, i8, i8 }
%struct.libraw_thumbnail_t = type { i32, i16, i16, i32, i32, ptr }
%struct.libraw_thumbnail_list_t = type { i32, [8 x %struct.libraw_thumbnail_item_t] }
%struct.libraw_thumbnail_item_t = type { i32, i16, i16, i16, i32, i32, i64 }
%struct.libraw_rawdata_t = type { ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %struct.libraw_iparams_t, %struct.libraw_image_sizes_t, %struct.libraw_internal_output_params_t, %struct.libraw_colordata_t }
%struct.libraw_internal_output_params_t = type { i32, i32, i32, i16, i16 }
%struct.libraw_internal_data_t = type { %struct.internal_data_t, %struct.libraw_internal_output_params_t, %struct.output_data_t, %struct.identify_data_t, %struct.unpacker_data_t }
%struct.internal_data_t = type { ptr, ptr, i32, ptr, i64, i64, [4 x i32] }
%struct.output_data_t = type { ptr, ptr }
%struct.identify_data_t = type { i32, i64, i64, i32, i32, i32 }
%struct.unpacker_data_t = type { i16, [4 x i16], [3 x i16], i32, i64, i64, i64, i64, i64, i64, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i64, i32, i32, i32, i32, i32, i32, i32, i32, i32, [16 x %struct.crx_data_header_t], i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32, [20 x i32], i16 }
%struct.crx_data_header_t = type { i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i64, i32, ptr, i32, i32, i32, ptr, i32, ptr }
%struct.decode = type { [2 x ptr], i32 }
%struct.tiff_ifd_t = type { i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, ptr, i32, ptr, i32, i32, i32, i32, i32, i32, i32, float, i64, i64, i32, [2 x %struct.libraw_dng_color_t], %struct.libraw_dng_levels_t, i32 }
%class.libraw_memmgr = type <{ ptr, i32, [4 x i8] }>
%struct.libraw_callbacks_t = type { ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }

@_ZTI17LibRaw_exceptions = external constant { ptr, ptr }, align 8

declare i32 @__gxx_personality_v0(...)

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #0

; Function Attrs: nounwind memory(none)
declare i32 @llvm.eh.typeid.for(ptr) #1

declare ptr @__cxa_begin_catch(ptr)

declare void @__cxa_end_catch()

; Function Attrs: mustprogress noinline optnone uwtable
declare noundef i32 @_ZN6LibRaw3FCFEii(ptr noundef nonnull align 8 dereferenceable(767320), i32 noundef, i32 noundef) #2 align 2

; Function Attrs: mustprogress noinline nounwind optnone uwtable
declare noundef i32 @_ZN6LibRaw2FCEii(ptr noundef nonnull align 8 dereferenceable(767320), i32 noundef, i32 noundef) #3 align 2

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memmove.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1 immarg) #4

declare ptr @__cxa_allocate_exception(i64)

declare void @__cxa_throw(ptr, ptr, ptr)

; Function Attrs: cold noreturn nounwind memory(inaccessiblemem: write)
declare void @llvm.trap() #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #6

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw18canon_600_load_rawEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw17canon_600_correctEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare noundef i32 @_ZN6LibRaw17phase_one_correctEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: nounwind
declare double @sqrt(double noundef) #7

; Function Attrs: mustprogress noinline nounwind optnone uwtable
declare void @_ZN6LibRaw15raw2image_startEv(ptr noundef nonnull align 8 dereferenceable(767320)) #3 align 2

; Function Attrs: mustprogress noinline optnone uwtable
define noundef i32 @_ZN6LibRaw12raw2image_exEi(ptr noundef nonnull align 8 dereferenceable(767320) %0, i32 noundef %1) #2 align 2 personality ptr @__gxx_personality_v0 !dbg !1328 {
  %3 = alloca i32, align 4
  %4 = alloca ptr, align 8
  %5 = alloca i32, align 4
  %6 = alloca ptr, align 8
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca [4 x i32], align 16
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca %struct.libraw_decoder_info_t.972, align 8
  %21 = alloca [4 x i16], align 2
  %22 = alloca i16, align 2
  %23 = alloca i32, align 4
  %24 = alloca i32, align 4
  %25 = alloca i32, align 4
  %26 = alloca i32, align 4
  %27 = alloca i32, align 4
  %28 = alloca i32, align 4
  %29 = alloca i32, align 4
  %30 = alloca i32, align 4
  %31 = alloca i32, align 4
  %32 = alloca i16, align 2
  %33 = alloca i32, align 4
  %34 = alloca i32, align 4
  %35 = alloca ptr, align 8
  %36 = alloca i32, align 4
  %37 = alloca ptr, align 8
  %38 = alloca ptr, align 8
  %39 = alloca i32, align 4
  %40 = alloca i32, align 4
  %41 = alloca ptr, align 8
  %42 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
  call void @llvm.dbg.declare(metadata ptr %4, metadata !1337, metadata !DIExpression()), !dbg !1339
  store i32 %1, ptr %5, align 4
  call void @llvm.dbg.declare(metadata ptr %5, metadata !1340, metadata !DIExpression()), !dbg !1341
  %43 = load ptr, ptr %4, align 8
  br label %44, !dbg !1342

44:                                               ; preds = %2
  %45 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1343
  %46 = getelementptr inbounds %struct.libraw_data_t, ptr %45, i32 0, i32 8, !dbg !1343
  %47 = load i32, ptr %46, align 8, !dbg !1343
  %48 = and i32 %47, 268435455, !dbg !1343
  %49 = icmp ult i32 %48, 8, !dbg !1343
  br i1 %49, label %50, label %51, !dbg !1346

50:                                               ; preds = %44
  store i32 -4, ptr %3, align 4, !dbg !1343
  br label %1320, !dbg !1343

51:                                               ; preds = %44
  br label %52, !dbg !1346

52:                                               ; preds = %51
  call void @_ZN6LibRaw15raw2image_startEv(ptr noundef nonnull align 8 dereferenceable(767320) %43), !dbg !1347
  %53 = bitcast ptr %43 to ptr, !dbg !1349
  %54 = load ptr, ptr %53, align 8, !dbg !1349
  %55 = getelementptr inbounds ptr, ptr %54, i64 10, !dbg !1349
  %56 = load ptr, ptr %55, align 8, !dbg !1349
  %57 = invoke noundef i32 %56(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %58 unwind label %84, !dbg !1349

58:                                               ; preds = %52
  %59 = icmp ne i32 %57, 0, !dbg !1349
  br i1 %59, label %60, label %106, !dbg !1351

60:                                               ; preds = %58
  %61 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1352
  %62 = getelementptr inbounds %struct.libraw_data_t, ptr %61, i32 0, i32 14, !dbg !1353
  %63 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %62, i32 0, i32 0, !dbg !1354
  %64 = load ptr, ptr %63, align 8, !dbg !1354
  %65 = icmp ne ptr %64, null, !dbg !1352
  br i1 %65, label %66, label %106, !dbg !1355

66:                                               ; preds = %60
  invoke void @_ZN6LibRaw29phase_one_allocate_tempbufferEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %67 unwind label %84, !dbg !1356

67:                                               ; preds = %66
  call void @llvm.dbg.declare(metadata ptr %8, metadata !1358, metadata !DIExpression()), !dbg !1359
  %68 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1360
  %69 = getelementptr inbounds %struct.libraw_data_t, ptr %68, i32 0, i32 14, !dbg !1361
  %70 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %69, i32 0, i32 0, !dbg !1362
  %71 = load ptr, ptr %70, align 8, !dbg !1362
  %72 = bitcast ptr %71 to ptr, !dbg !1363
  %73 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1364
  %74 = getelementptr inbounds %struct.libraw_data_t, ptr %73, i32 0, i32 14, !dbg !1365
  %75 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %74, i32 0, i32 1, !dbg !1366
  %76 = load ptr, ptr %75, align 8, !dbg !1366
  %77 = invoke noundef i32 @_ZN6LibRaw24phase_one_subtract_blackEPtS0_(ptr noundef nonnull align 8 dereferenceable(767320) %43, ptr noundef %72, ptr noundef %76)
          to label %78 unwind label %84, !dbg !1367

78:                                               ; preds = %67
  store i32 %77, ptr %8, align 4, !dbg !1359
  %79 = load i32, ptr %8, align 4, !dbg !1368
  %80 = icmp eq i32 %79, 0, !dbg !1370
  br i1 %80, label %81, label %99, !dbg !1371

81:                                               ; preds = %78
  %82 = invoke noundef i32 @_ZN6LibRaw17phase_one_correctEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %83 unwind label %84, !dbg !1372

83:                                               ; preds = %81
  store i32 %82, ptr %8, align 4, !dbg !1373
  br label %99, !dbg !1374

84:                                               ; preds = %1249, %1225, %1217, %1212, %1010, %1002, %842, %543, %533, %525, %505, %397, %300, %102, %81, %67, %66, %52
  %85 = landingpad { ptr, i32 }
          catch ptr @_ZTI17LibRaw_exceptions, !dbg !1375
  %86 = extractvalue { ptr, i32 } %85, 0, !dbg !1375
  store ptr %86, ptr %6, align 8, !dbg !1375
  %87 = extractvalue { ptr, i32 } %85, 1, !dbg !1375
  store i32 %87, ptr %7, align 4, !dbg !1375
  br label %88, !dbg !1375

88:                                               ; preds = %84
  %89 = load i32, ptr %7, align 4, !dbg !1376
  %90 = call i32 @llvm.eh.typeid.for(ptr @_ZTI17LibRaw_exceptions) #8, !dbg !1376
  %91 = icmp eq i32 %89, %90, !dbg !1376
  br i1 %91, label %92, label %1322, !dbg !1376

92:                                               ; preds = %88
  call void @llvm.dbg.declare(metadata ptr %41, metadata !1377, metadata !DIExpression()), !dbg !1380
  %93 = load ptr, ptr %6, align 8, !dbg !1376
  %94 = call ptr @__cxa_begin_catch(ptr %93) #8, !dbg !1376
  %95 = bitcast ptr %94 to ptr, !dbg !1376
  store ptr %95, ptr %41, align 8, !dbg !1376
  br label %96, !dbg !1381

96:                                               ; preds = %92
  %97 = load ptr, ptr %41, align 8, !dbg !1383
  %98 = load i32, ptr %97, align 4, !dbg !1383
  switch i32 %98, label %1313 [
    i32 11, label %1291
    i32 1, label %1297
    i32 10, label %1299
    i32 2, label %1301
    i32 3, label %1301
    i32 9, label %1303
    i32 4, label %1305
    i32 5, label %1305
    i32 6, label %1307
    i32 7, label %1309
    i32 12, label %1311
  ], !dbg !1383

99:                                               ; preds = %83, %78
  %100 = load i32, ptr %8, align 4, !dbg !1385
  %101 = icmp ne i32 %100, 0, !dbg !1387
  br i1 %101, label %102, label %105, !dbg !1388

102:                                              ; preds = %99
  invoke void @_ZN6LibRaw25phase_one_free_tempbufferEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %103 unwind label %84, !dbg !1389

103:                                              ; preds = %102
  %104 = load i32, ptr %8, align 4, !dbg !1391
  store i32 %104, ptr %3, align 4, !dbg !1392
  br label %1320, !dbg !1392

105:                                              ; preds = %99
  br label %106, !dbg !1393

106:                                              ; preds = %105, %60, %58
  call void @llvm.dbg.declare(metadata ptr %9, metadata !1394, metadata !DIExpression()), !dbg !1395
  store i32 0, ptr %9, align 4, !dbg !1395
  %107 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1396
  %108 = getelementptr inbounds %struct.libraw_data_t, ptr %107, i32 0, i32 6, !dbg !1396
  %109 = getelementptr inbounds %struct.libraw_output_params_t, ptr %108, i32 0, i32 1, !dbg !1398
  %110 = getelementptr inbounds [4 x i32], ptr %109, i64 0, i64 2, !dbg !1396
  %111 = load i32, ptr %110, align 8, !dbg !1396
  %112 = xor i32 %111, -1, !dbg !1399
  %113 = icmp ne i32 %112, 0, !dbg !1399
  br i1 %113, label %114, label %424, !dbg !1400

114:                                              ; preds = %106
  %115 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1401
  %116 = getelementptr inbounds %struct.libraw_data_t, ptr %115, i32 0, i32 6, !dbg !1401
  %117 = getelementptr inbounds %struct.libraw_output_params_t, ptr %116, i32 0, i32 1, !dbg !1402
  %118 = getelementptr inbounds [4 x i32], ptr %117, i64 0, i64 3, !dbg !1401
  %119 = load i32, ptr %118, align 4, !dbg !1401
  %120 = xor i32 %119, -1, !dbg !1403
  %121 = icmp ne i32 %120, 0, !dbg !1403
  br i1 %121, label %122, label %424, !dbg !1404

122:                                              ; preds = %114
  call void @llvm.dbg.declare(metadata ptr %10, metadata !1405, metadata !DIExpression()), !dbg !1408
  call void @llvm.dbg.declare(metadata ptr %11, metadata !1409, metadata !DIExpression()), !dbg !1410
  call void @llvm.dbg.declare(metadata ptr %12, metadata !1411, metadata !DIExpression()), !dbg !1412
  call void @llvm.dbg.declare(metadata ptr %13, metadata !1413, metadata !DIExpression()), !dbg !1415
  store i32 0, ptr %13, align 4, !dbg !1415
  br label %123, !dbg !1416

123:                                              ; preds = %147, %122
  %124 = load i32, ptr %13, align 4, !dbg !1417
  %125 = icmp slt i32 %124, 4, !dbg !1419
  br i1 %125, label %126, label %150, !dbg !1420

126:                                              ; preds = %123
  %127 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1421
  %128 = getelementptr inbounds %struct.libraw_data_t, ptr %127, i32 0, i32 6, !dbg !1421
  %129 = getelementptr inbounds %struct.libraw_output_params_t, ptr %128, i32 0, i32 1, !dbg !1423
  %130 = load i32, ptr %13, align 4, !dbg !1424
  %131 = sext i32 %130 to i64, !dbg !1421
  %132 = getelementptr inbounds [4 x i32], ptr %129, i64 0, i64 %131, !dbg !1421
  %133 = load i32, ptr %132, align 4, !dbg !1421
  %134 = load i32, ptr %13, align 4, !dbg !1425
  %135 = sext i32 %134 to i64, !dbg !1426
  %136 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 %135, !dbg !1426
  store i32 %133, ptr %136, align 4, !dbg !1427
  %137 = load i32, ptr %13, align 4, !dbg !1428
  %138 = sext i32 %137 to i64, !dbg !1430
  %139 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 %138, !dbg !1430
  %140 = load i32, ptr %139, align 4, !dbg !1430
  %141 = icmp slt i32 %140, 0, !dbg !1431
  br i1 %141, label %142, label %146, !dbg !1432

142:                                              ; preds = %126
  %143 = load i32, ptr %13, align 4, !dbg !1433
  %144 = sext i32 %143 to i64, !dbg !1434
  %145 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 %144, !dbg !1434
  store i32 0, ptr %145, align 4, !dbg !1435
  br label %146, !dbg !1434

146:                                              ; preds = %142, %126
  br label %147, !dbg !1436

147:                                              ; preds = %146
  %148 = load i32, ptr %13, align 4, !dbg !1437
  %149 = add nsw i32 %148, 1, !dbg !1437
  store i32 %149, ptr %13, align 4, !dbg !1437
  br label %123, !dbg !1438, !llvm.loop !1439

150:                                              ; preds = %123
  %151 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1442
  %152 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %151, i32 0, i32 1, !dbg !1442
  %153 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %152, i32 0, i32 4, !dbg !1444
  %154 = load i16, ptr %153, align 2, !dbg !1444
  %155 = icmp ne i16 %154, 0, !dbg !1442
  br i1 %155, label %156, label %204, !dbg !1445

156:                                              ; preds = %150
  %157 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1446
  %158 = getelementptr inbounds %struct.libraw_data_t, ptr %157, i32 0, i32 2, !dbg !1447
  %159 = getelementptr inbounds %struct.libraw_iparams_t, ptr %158, i32 0, i32 11, !dbg !1448
  %160 = load i32, ptr %159, align 8, !dbg !1448
  %161 = icmp uge i32 %160, 1000, !dbg !1449
  br i1 %161, label %162, label %204, !dbg !1450

162:                                              ; preds = %156
  %163 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1451
  %164 = load i32, ptr %163, align 16, !dbg !1451
  %165 = sdiv i32 %164, 4, !dbg !1453
  %166 = mul nsw i32 %165, 4, !dbg !1454
  %167 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1455
  store i32 %166, ptr %167, align 16, !dbg !1456
  %168 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1457
  %169 = load i32, ptr %168, align 4, !dbg !1457
  %170 = sdiv i32 %169, 4, !dbg !1458
  %171 = mul nsw i32 %170, 4, !dbg !1459
  %172 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1460
  store i32 %171, ptr %172, align 4, !dbg !1461
  %173 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1462
  %174 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %173, i32 0, i32 4, !dbg !1464
  %175 = getelementptr inbounds %struct.unpacker_data_t, ptr %174, i32 0, i32 16, !dbg !1465
  %176 = load i32, ptr %175, align 8, !dbg !1465
  %177 = icmp ne i32 %176, 0, !dbg !1462
  br i1 %177, label %191, label %178, !dbg !1466

178:                                              ; preds = %162
  %179 = call double @sqrt(double noundef 2.000000e+00) #8, !dbg !1467
  %180 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1469
  %181 = load i32, ptr %180, align 8, !dbg !1470
  %182 = sitofp i32 %181 to double, !dbg !1470
  %183 = fmul double %182, %179, !dbg !1470
  %184 = fptosi double %183 to i32, !dbg !1470
  store i32 %184, ptr %180, align 8, !dbg !1470
  %185 = call double @sqrt(double noundef 2.000000e+00) #8, !dbg !1471
  %186 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1472
  %187 = load i32, ptr %186, align 4, !dbg !1473
  %188 = sitofp i32 %187 to double, !dbg !1473
  %189 = fdiv double %188, %185, !dbg !1473
  %190 = fptosi double %189 to i32, !dbg !1473
  store i32 %190, ptr %186, align 4, !dbg !1473
  br label %191, !dbg !1474

191:                                              ; preds = %178, %162
  %192 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1475
  %193 = load i32, ptr %192, align 8, !dbg !1475
  %194 = sdiv i32 %193, 4, !dbg !1476
  %195 = add nsw i32 %194, 1, !dbg !1477
  %196 = mul nsw i32 %195, 4, !dbg !1478
  %197 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1479
  store i32 %196, ptr %197, align 8, !dbg !1480
  %198 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1481
  %199 = load i32, ptr %198, align 4, !dbg !1481
  %200 = sdiv i32 %199, 4, !dbg !1482
  %201 = add nsw i32 %200, 1, !dbg !1483
  %202 = mul nsw i32 %201, 4, !dbg !1484
  %203 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1485
  store i32 %202, ptr %203, align 4, !dbg !1486
  br label %240, !dbg !1487

204:                                              ; preds = %156, %150
  %205 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1488
  %206 = getelementptr inbounds %struct.libraw_data_t, ptr %205, i32 0, i32 2, !dbg !1490
  %207 = getelementptr inbounds %struct.libraw_iparams_t, ptr %206, i32 0, i32 11, !dbg !1491
  %208 = load i32, ptr %207, align 8, !dbg !1491
  %209 = icmp eq i32 %208, 1, !dbg !1492
  br i1 %209, label %210, label %221, !dbg !1493

210:                                              ; preds = %204
  %211 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1494
  %212 = load i32, ptr %211, align 16, !dbg !1494
  %213 = sdiv i32 %212, 16, !dbg !1496
  %214 = mul nsw i32 %213, 16, !dbg !1497
  %215 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1498
  store i32 %214, ptr %215, align 16, !dbg !1499
  %216 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1500
  %217 = load i32, ptr %216, align 4, !dbg !1500
  %218 = sdiv i32 %217, 16, !dbg !1501
  %219 = mul nsw i32 %218, 16, !dbg !1502
  %220 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1503
  store i32 %219, ptr %220, align 4, !dbg !1504
  br label %239, !dbg !1505

221:                                              ; preds = %204
  %222 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1506
  %223 = getelementptr inbounds %struct.libraw_data_t, ptr %222, i32 0, i32 2, !dbg !1508
  %224 = getelementptr inbounds %struct.libraw_iparams_t, ptr %223, i32 0, i32 11, !dbg !1509
  %225 = load i32, ptr %224, align 8, !dbg !1509
  %226 = icmp eq i32 %225, 9, !dbg !1510
  br i1 %226, label %227, label %238, !dbg !1511

227:                                              ; preds = %221
  %228 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1512
  %229 = load i32, ptr %228, align 16, !dbg !1512
  %230 = sdiv i32 %229, 6, !dbg !1514
  %231 = mul nsw i32 %230, 6, !dbg !1515
  %232 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1516
  store i32 %231, ptr %232, align 16, !dbg !1517
  %233 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1518
  %234 = load i32, ptr %233, align 4, !dbg !1518
  %235 = sdiv i32 %234, 6, !dbg !1519
  %236 = mul nsw i32 %235, 6, !dbg !1520
  %237 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1521
  store i32 %236, ptr %237, align 4, !dbg !1522
  br label %238, !dbg !1523

238:                                              ; preds = %227, %221
  br label %239

239:                                              ; preds = %238, %210
  br label %240

240:                                              ; preds = %239, %191
  store i32 1, ptr %9, align 4, !dbg !1524
  %241 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1525
  %242 = load i32, ptr %241, align 8, !dbg !1525
  %243 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1525
  %244 = getelementptr inbounds %struct.libraw_data_t, ptr %243, i32 0, i32 1, !dbg !1525
  %245 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %244, i32 0, i32 3, !dbg !1525
  %246 = load i16, ptr %245, align 2, !dbg !1525
  %247 = zext i16 %246 to i32, !dbg !1525
  %248 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1525
  %249 = load i32, ptr %248, align 16, !dbg !1525
  %250 = sub nsw i32 %247, %249, !dbg !1525
  %251 = icmp slt i32 %242, %250, !dbg !1525
  br i1 %251, label %252, label %255, !dbg !1525

252:                                              ; preds = %240
  %253 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1525
  %254 = load i32, ptr %253, align 8, !dbg !1525
  br label %264, !dbg !1525

255:                                              ; preds = %240
  %256 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1525
  %257 = getelementptr inbounds %struct.libraw_data_t, ptr %256, i32 0, i32 1, !dbg !1525
  %258 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %257, i32 0, i32 3, !dbg !1525
  %259 = load i16, ptr %258, align 2, !dbg !1525
  %260 = zext i16 %259 to i32, !dbg !1525
  %261 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1525
  %262 = load i32, ptr %261, align 16, !dbg !1525
  %263 = sub nsw i32 %260, %262, !dbg !1525
  br label %264, !dbg !1525

264:                                              ; preds = %255, %252
  %265 = phi i32 [ %254, %252 ], [ %263, %255 ], !dbg !1525
  %266 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1526
  store i32 %265, ptr %266, align 8, !dbg !1527
  %267 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1528
  %268 = load i32, ptr %267, align 4, !dbg !1528
  %269 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1528
  %270 = getelementptr inbounds %struct.libraw_data_t, ptr %269, i32 0, i32 1, !dbg !1528
  %271 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %270, i32 0, i32 2, !dbg !1528
  %272 = load i16, ptr %271, align 4, !dbg !1528
  %273 = zext i16 %272 to i32, !dbg !1528
  %274 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1528
  %275 = load i32, ptr %274, align 4, !dbg !1528
  %276 = sub nsw i32 %273, %275, !dbg !1528
  %277 = icmp slt i32 %268, %276, !dbg !1528
  br i1 %277, label %278, label %281, !dbg !1528

278:                                              ; preds = %264
  %279 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1528
  %280 = load i32, ptr %279, align 4, !dbg !1528
  br label %290, !dbg !1528

281:                                              ; preds = %264
  %282 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1528
  %283 = getelementptr inbounds %struct.libraw_data_t, ptr %282, i32 0, i32 1, !dbg !1528
  %284 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %283, i32 0, i32 2, !dbg !1528
  %285 = load i16, ptr %284, align 4, !dbg !1528
  %286 = zext i16 %285 to i32, !dbg !1528
  %287 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1528
  %288 = load i32, ptr %287, align 4, !dbg !1528
  %289 = sub nsw i32 %286, %288, !dbg !1528
  br label %290, !dbg !1528

290:                                              ; preds = %281, %278
  %291 = phi i32 [ %280, %278 ], [ %289, %281 ], !dbg !1528
  %292 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1529
  store i32 %291, ptr %292, align 4, !dbg !1530
  %293 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1531
  %294 = load i32, ptr %293, align 8, !dbg !1531
  %295 = icmp sle i32 %294, 0, !dbg !1533
  br i1 %295, label %300, label %296, !dbg !1534

296:                                              ; preds = %290
  %297 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1535
  %298 = load i32, ptr %297, align 4, !dbg !1535
  %299 = icmp sle i32 %298, 0, !dbg !1536
  br i1 %299, label %300, label %303, !dbg !1537

300:                                              ; preds = %296, %290
  %301 = call ptr @__cxa_allocate_exception(i64 4) #8, !dbg !1538
  %302 = bitcast ptr %301 to ptr, !dbg !1538
  store i32 7, ptr %302, align 16, !dbg !1538
  invoke void @__cxa_throw(ptr %301, ptr @_ZTI17LibRaw_exceptions, ptr null) #9
          to label %1327 unwind label %84, !dbg !1538

303:                                              ; preds = %296
  %304 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1539
  %305 = load i32, ptr %304, align 16, !dbg !1539
  %306 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1540
  %307 = getelementptr inbounds %struct.libraw_data_t, ptr %306, i32 0, i32 1, !dbg !1540
  %308 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %307, i32 0, i32 5, !dbg !1541
  %309 = load i16, ptr %308, align 2, !dbg !1542
  %310 = zext i16 %309 to i32, !dbg !1542
  %311 = add nsw i32 %310, %305, !dbg !1542
  %312 = trunc i32 %311 to i16, !dbg !1542
  store i16 %312, ptr %308, align 2, !dbg !1542
  %313 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1543
  %314 = load i32, ptr %313, align 4, !dbg !1543
  %315 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1544
  %316 = getelementptr inbounds %struct.libraw_data_t, ptr %315, i32 0, i32 1, !dbg !1544
  %317 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %316, i32 0, i32 4, !dbg !1545
  %318 = load i16, ptr %317, align 8, !dbg !1546
  %319 = zext i16 %318 to i32, !dbg !1546
  %320 = add nsw i32 %319, %314, !dbg !1546
  %321 = trunc i32 %320 to i16, !dbg !1546
  store i16 %321, ptr %317, align 8, !dbg !1546
  %322 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 2, !dbg !1547
  %323 = load i32, ptr %322, align 8, !dbg !1547
  %324 = trunc i32 %323 to i16, !dbg !1547
  %325 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1548
  %326 = getelementptr inbounds %struct.libraw_data_t, ptr %325, i32 0, i32 1, !dbg !1548
  %327 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %326, i32 0, i32 3, !dbg !1549
  store i16 %324, ptr %327, align 2, !dbg !1550
  %328 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 3, !dbg !1551
  %329 = load i32, ptr %328, align 4, !dbg !1551
  %330 = trunc i32 %329 to i16, !dbg !1551
  %331 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1552
  %332 = getelementptr inbounds %struct.libraw_data_t, ptr %331, i32 0, i32 1, !dbg !1552
  %333 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %332, i32 0, i32 2, !dbg !1553
  store i16 %330, ptr %333, align 4, !dbg !1554
  %334 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1555
  %335 = getelementptr inbounds %struct.libraw_data_t, ptr %334, i32 0, i32 1, !dbg !1555
  %336 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %335, i32 0, i32 2, !dbg !1556
  %337 = load i16, ptr %336, align 4, !dbg !1556
  %338 = zext i16 %337 to i32, !dbg !1555
  %339 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1557
  %340 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %339, i32 0, i32 1, !dbg !1557
  %341 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %340, i32 0, i32 3, !dbg !1558
  %342 = load i16, ptr %341, align 4, !dbg !1558
  %343 = zext i16 %342 to i32, !dbg !1557
  %344 = add nsw i32 %338, %343, !dbg !1559
  %345 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1560
  %346 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %345, i32 0, i32 1, !dbg !1560
  %347 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %346, i32 0, i32 3, !dbg !1561
  %348 = load i16, ptr %347, align 4, !dbg !1561
  %349 = zext i16 %348 to i32, !dbg !1560
  %350 = ashr i32 %344, %349, !dbg !1562
  %351 = trunc i32 %350 to i16, !dbg !1563
  %352 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1564
  %353 = getelementptr inbounds %struct.libraw_data_t, ptr %352, i32 0, i32 1, !dbg !1564
  %354 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %353, i32 0, i32 6, !dbg !1565
  store i16 %351, ptr %354, align 4, !dbg !1566
  %355 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1567
  %356 = getelementptr inbounds %struct.libraw_data_t, ptr %355, i32 0, i32 1, !dbg !1567
  %357 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %356, i32 0, i32 3, !dbg !1568
  %358 = load i16, ptr %357, align 2, !dbg !1568
  %359 = zext i16 %358 to i32, !dbg !1567
  %360 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1569
  %361 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %360, i32 0, i32 1, !dbg !1569
  %362 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %361, i32 0, i32 3, !dbg !1570
  %363 = load i16, ptr %362, align 4, !dbg !1570
  %364 = zext i16 %363 to i32, !dbg !1569
  %365 = add nsw i32 %359, %364, !dbg !1571
  %366 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1572
  %367 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %366, i32 0, i32 1, !dbg !1572
  %368 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %367, i32 0, i32 3, !dbg !1573
  %369 = load i16, ptr %368, align 4, !dbg !1573
  %370 = zext i16 %369 to i32, !dbg !1572
  %371 = ashr i32 %365, %370, !dbg !1574
  %372 = trunc i32 %371 to i16, !dbg !1575
  %373 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1576
  %374 = getelementptr inbounds %struct.libraw_data_t, ptr %373, i32 0, i32 1, !dbg !1576
  %375 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %374, i32 0, i32 7, !dbg !1577
  store i16 %372, ptr %375, align 2, !dbg !1578
  %376 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1579
  %377 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %376, i32 0, i32 1, !dbg !1579
  %378 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %377, i32 0, i32 4, !dbg !1581
  %379 = load i16, ptr %378, align 2, !dbg !1581
  %380 = icmp ne i16 %379, 0, !dbg !1579
  br i1 %380, label %423, label %381, !dbg !1582

381:                                              ; preds = %303
  %382 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1583
  %383 = getelementptr inbounds %struct.libraw_data_t, ptr %382, i32 0, i32 2, !dbg !1584
  %384 = getelementptr inbounds %struct.libraw_iparams_t, ptr %383, i32 0, i32 11, !dbg !1585
  %385 = load i32, ptr %384, align 8, !dbg !1585
  %386 = icmp ne i32 %385, 0, !dbg !1583
  br i1 %386, label %387, label %423, !dbg !1586

387:                                              ; preds = %381
  %388 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1587
  %389 = getelementptr inbounds %struct.libraw_data_t, ptr %388, i32 0, i32 2, !dbg !1588
  %390 = getelementptr inbounds %struct.libraw_iparams_t, ptr %389, i32 0, i32 11, !dbg !1589
  %391 = load i32, ptr %390, align 8, !dbg !1589
  %392 = icmp uge i32 %391, 1000, !dbg !1590
  br i1 %392, label %393, label %423, !dbg !1591

393:                                              ; preds = %387
  store i32 0, ptr %11, align 4, !dbg !1592
  store i32 0, ptr %12, align 4, !dbg !1595
  br label %394, !dbg !1596

394:                                              ; preds = %415, %393
  %395 = load i32, ptr %11, align 4, !dbg !1597
  %396 = icmp slt i32 %395, 16, !dbg !1599
  br i1 %396, label %397, label %418, !dbg !1600

397:                                              ; preds = %394
  %398 = load i32, ptr %11, align 4, !dbg !1601
  %399 = ashr i32 %398, 1, !dbg !1602
  %400 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 1, !dbg !1603
  %401 = load i32, ptr %400, align 4, !dbg !1603
  %402 = add nsw i32 %399, %401, !dbg !1604
  %403 = load i32, ptr %11, align 4, !dbg !1605
  %404 = and i32 %403, 1, !dbg !1606
  %405 = getelementptr inbounds [4 x i32], ptr %10, i64 0, i64 0, !dbg !1607
  %406 = load i32, ptr %405, align 16, !dbg !1607
  %407 = add nsw i32 %404, %406, !dbg !1608
  %408 = invoke noundef i32 @_ZN6LibRaw2FCEii(ptr noundef nonnull align 8 dereferenceable(767320) %43, i32 noundef %402, i32 noundef %407)
          to label %409 unwind label %84, !dbg !1609

409:                                              ; preds = %397
  %410 = load i32, ptr %11, align 4, !dbg !1610
  %411 = mul nsw i32 %410, 2, !dbg !1611
  %412 = shl i32 %408, %411, !dbg !1612
  %413 = load i32, ptr %12, align 4, !dbg !1613
  %414 = or i32 %413, %412, !dbg !1613
  store i32 %414, ptr %12, align 4, !dbg !1613
  br label %415, !dbg !1614

415:                                              ; preds = %409
  %416 = load i32, ptr %11, align 4, !dbg !1615
  %417 = add nsw i32 %416, 1, !dbg !1615
  store i32 %417, ptr %11, align 4, !dbg !1615
  br label %394, !dbg !1616, !llvm.loop !1617

418:                                              ; preds = %394
  %419 = load i32, ptr %12, align 4, !dbg !1619
  %420 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1620
  %421 = getelementptr inbounds %struct.libraw_data_t, ptr %420, i32 0, i32 2, !dbg !1621
  %422 = getelementptr inbounds %struct.libraw_iparams_t, ptr %421, i32 0, i32 11, !dbg !1622
  store i32 %419, ptr %422, align 8, !dbg !1623
  br label %423, !dbg !1624

423:                                              ; preds = %418, %387, %381, %303
  br label %424, !dbg !1625

424:                                              ; preds = %423, %114, %106
  call void @llvm.dbg.declare(metadata ptr %14, metadata !1626, metadata !DIExpression()), !dbg !1627
  %425 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1628
  %426 = getelementptr inbounds %struct.libraw_data_t, ptr %425, i32 0, i32 1, !dbg !1628
  %427 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %426, i32 0, i32 7, !dbg !1629
  %428 = load i16, ptr %427, align 2, !dbg !1629
  %429 = zext i16 %428 to i32, !dbg !1628
  store i32 %429, ptr %14, align 4, !dbg !1627
  call void @llvm.dbg.declare(metadata ptr %15, metadata !1630, metadata !DIExpression()), !dbg !1631
  %430 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1632
  %431 = getelementptr inbounds %struct.libraw_data_t, ptr %430, i32 0, i32 1, !dbg !1632
  %432 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %431, i32 0, i32 6, !dbg !1633
  %433 = load i16, ptr %432, align 4, !dbg !1633
  %434 = zext i16 %433 to i32, !dbg !1632
  store i32 %434, ptr %15, align 4, !dbg !1631
  %435 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1634
  %436 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %435, i32 0, i32 1, !dbg !1634
  %437 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %436, i32 0, i32 4, !dbg !1636
  %438 = load i16, ptr %437, align 2, !dbg !1636
  %439 = icmp ne i16 %438, 0, !dbg !1634
  br i1 %439, label %440, label %497, !dbg !1637

440:                                              ; preds = %424
  %441 = load i32, ptr %9, align 4, !dbg !1638
  %442 = icmp ne i32 %441, 0, !dbg !1638
  br i1 %442, label %443, label %497, !dbg !1639

443:                                              ; preds = %440
  call void @llvm.dbg.declare(metadata ptr %16, metadata !1640, metadata !DIExpression()), !dbg !1642
  %444 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1643
  %445 = getelementptr inbounds %struct.libraw_data_t, ptr %444, i32 0, i32 1, !dbg !1643
  %446 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %445, i32 0, i32 3, !dbg !1644
  %447 = load i16, ptr %446, align 2, !dbg !1644
  %448 = zext i16 %447 to i32, !dbg !1643
  %449 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1645
  %450 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %449, i32 0, i32 4, !dbg !1646
  %451 = getelementptr inbounds %struct.unpacker_data_t, ptr %450, i32 0, i32 16, !dbg !1647
  %452 = load i32, ptr %451, align 8, !dbg !1647
  %453 = icmp ne i32 %452, 0, !dbg !1645
  %454 = xor i1 %453, true, !dbg !1648
  %455 = zext i1 %454 to i32, !dbg !1648
  %456 = ashr i32 %448, %455, !dbg !1649
  store i32 %456, ptr %16, align 4, !dbg !1642
  call void @llvm.dbg.declare(metadata ptr %17, metadata !1650, metadata !DIExpression()), !dbg !1651
  %457 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1652
  %458 = getelementptr inbounds %struct.libraw_data_t, ptr %457, i32 0, i32 1, !dbg !1652
  %459 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %458, i32 0, i32 2, !dbg !1653
  %460 = load i16, ptr %459, align 4, !dbg !1653
  %461 = zext i16 %460 to i32, !dbg !1652
  %462 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1654
  %463 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %462, i32 0, i32 4, !dbg !1655
  %464 = getelementptr inbounds %struct.unpacker_data_t, ptr %463, i32 0, i32 16, !dbg !1656
  %465 = load i32, ptr %464, align 8, !dbg !1656
  %466 = ashr i32 %461, %465, !dbg !1657
  %467 = load i32, ptr %16, align 4, !dbg !1658
  %468 = add nsw i32 %466, %467, !dbg !1659
  store i32 %468, ptr %17, align 4, !dbg !1651
  call void @llvm.dbg.declare(metadata ptr %18, metadata !1660, metadata !DIExpression()), !dbg !1661
  %469 = load i32, ptr %17, align 4, !dbg !1662
  %470 = sub nsw i32 %469, 1, !dbg !1663
  store i32 %470, ptr %18, align 4, !dbg !1661
  %471 = load i32, ptr %18, align 4, !dbg !1664
  %472 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1665
  %473 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %472, i32 0, i32 1, !dbg !1665
  %474 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %473, i32 0, i32 3, !dbg !1666
  %475 = load i16, ptr %474, align 4, !dbg !1666
  %476 = zext i16 %475 to i32, !dbg !1665
  %477 = add nsw i32 %471, %476, !dbg !1667
  %478 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1668
  %479 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %478, i32 0, i32 1, !dbg !1668
  %480 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %479, i32 0, i32 3, !dbg !1669
  %481 = load i16, ptr %480, align 4, !dbg !1669
  %482 = zext i16 %481 to i32, !dbg !1668
  %483 = ashr i32 %477, %482, !dbg !1670
  store i32 %483, ptr %15, align 4, !dbg !1671
  %484 = load i32, ptr %17, align 4, !dbg !1672
  %485 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1673
  %486 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %485, i32 0, i32 1, !dbg !1673
  %487 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %486, i32 0, i32 3, !dbg !1674
  %488 = load i16, ptr %487, align 4, !dbg !1674
  %489 = zext i16 %488 to i32, !dbg !1673
  %490 = add nsw i32 %484, %489, !dbg !1675
  %491 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1676
  %492 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %491, i32 0, i32 1, !dbg !1676
  %493 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %492, i32 0, i32 3, !dbg !1677
  %494 = load i16, ptr %493, align 4, !dbg !1677
  %495 = zext i16 %494 to i32, !dbg !1676
  %496 = ashr i32 %490, %495, !dbg !1678
  store i32 %496, ptr %14, align 4, !dbg !1679
  br label %497, !dbg !1680

497:                                              ; preds = %443, %440, %424
  call void @llvm.dbg.declare(metadata ptr %19, metadata !1681, metadata !DIExpression()), !dbg !1682
  %498 = load i32, ptr %14, align 4, !dbg !1683
  %499 = load i32, ptr %15, align 4, !dbg !1684
  %500 = mul nsw i32 %498, %499, !dbg !1685
  store i32 %500, ptr %19, align 4, !dbg !1682
  %501 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1686
  %502 = getelementptr inbounds %struct.libraw_data_t, ptr %501, i32 0, i32 0, !dbg !1688
  %503 = load ptr, ptr %502, align 8, !dbg !1688
  %504 = icmp ne ptr %503, null, !dbg !1686
  br i1 %504, label %505, label %525, !dbg !1689

505:                                              ; preds = %497
  %506 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1690
  %507 = getelementptr inbounds %struct.libraw_data_t, ptr %506, i32 0, i32 0, !dbg !1692
  %508 = load ptr, ptr %507, align 8, !dbg !1692
  %509 = bitcast ptr %508 to ptr, !dbg !1690
  %510 = load i32, ptr %19, align 4, !dbg !1693
  %511 = sext i32 %510 to i64, !dbg !1693
  %512 = mul i64 %511, 8, !dbg !1694
  %513 = invoke noundef ptr @_ZN6LibRaw7reallocEPvm(ptr noundef nonnull align 8 dereferenceable(767320) %43, ptr noundef %509, i64 noundef %512)
          to label %514 unwind label %84, !dbg !1695

514:                                              ; preds = %505
  %515 = bitcast ptr %513 to ptr, !dbg !1696
  %516 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1697
  %517 = getelementptr inbounds %struct.libraw_data_t, ptr %516, i32 0, i32 0, !dbg !1698
  store ptr %515, ptr %517, align 8, !dbg !1699
  %518 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1700
  %519 = getelementptr inbounds %struct.libraw_data_t, ptr %518, i32 0, i32 0, !dbg !1701
  %520 = load ptr, ptr %519, align 8, !dbg !1701
  %521 = bitcast ptr %520 to ptr, !dbg !1702
  %522 = load i32, ptr %19, align 4, !dbg !1703
  %523 = sext i32 %522 to i64, !dbg !1703
  %524 = mul i64 %523, 8, !dbg !1704
  call void @llvm.memset.p0.i64(ptr align 2 %521, i8 0, i64 %524, i1 false), !dbg !1702
  br label %533, !dbg !1705

525:                                              ; preds = %497
  %526 = load i32, ptr %19, align 4, !dbg !1706
  %527 = sext i32 %526 to i64, !dbg !1706
  %528 = invoke noundef ptr @_ZN6LibRaw6callocEmm(ptr noundef nonnull align 8 dereferenceable(767320) %43, i64 noundef %527, i64 noundef 8)
          to label %529 unwind label %84, !dbg !1707

529:                                              ; preds = %525
  %530 = bitcast ptr %528 to ptr, !dbg !1708
  %531 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1709
  %532 = getelementptr inbounds %struct.libraw_data_t, ptr %531, i32 0, i32 0, !dbg !1710
  store ptr %530, ptr %532, align 8, !dbg !1711
  br label %533

533:                                              ; preds = %529, %514
  call void @llvm.dbg.declare(metadata ptr %20, metadata !1712, metadata !DIExpression()), !dbg !1718
  %534 = bitcast ptr %43 to ptr, !dbg !1719
  %535 = load ptr, ptr %534, align 8, !dbg !1719
  %536 = getelementptr inbounds ptr, ptr %535, i64 6, !dbg !1719
  %537 = load ptr, ptr %536, align 8, !dbg !1719
  %538 = invoke noundef i32 %537(ptr noundef nonnull align 8 dereferenceable(767320) %43, ptr noundef %20)
          to label %539 unwind label %84, !dbg !1719

539:                                              ; preds = %533
  call void @llvm.dbg.declare(metadata ptr %21, metadata !1720, metadata !DIExpression()), !dbg !1722
  %540 = bitcast ptr %21 to ptr, !dbg !1722
  call void @llvm.memset.p0.i64(ptr align 2 %540, i8 0, i64 8, i1 false), !dbg !1722
  call void @llvm.dbg.declare(metadata ptr %22, metadata !1723, metadata !DIExpression()), !dbg !1724
  store i16 0, ptr %22, align 2, !dbg !1724
  %541 = load i32, ptr %5, align 4, !dbg !1725
  %542 = icmp ne i32 %541, 0, !dbg !1725
  br i1 %542, label %543, label %564, !dbg !1727

543:                                              ; preds = %539
  invoke void @_ZN6LibRaw9adjust_blEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %544 unwind label %84, !dbg !1728

544:                                              ; preds = %543
  call void @llvm.dbg.declare(metadata ptr %23, metadata !1730, metadata !DIExpression()), !dbg !1732
  store i32 0, ptr %23, align 4, !dbg !1732
  br label %545, !dbg !1733

545:                                              ; preds = %560, %544
  %546 = load i32, ptr %23, align 4, !dbg !1734
  %547 = icmp slt i32 %546, 4, !dbg !1736
  br i1 %547, label %548, label %563, !dbg !1737

548:                                              ; preds = %545
  %549 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1738
  %550 = getelementptr inbounds %struct.libraw_data_t, ptr %549, i32 0, i32 10, !dbg !1738
  %551 = getelementptr inbounds %struct.libraw_colordata_t, ptr %550, i32 0, i32 1, !dbg !1739
  %552 = load i32, ptr %23, align 4, !dbg !1740
  %553 = sext i32 %552 to i64, !dbg !1738
  %554 = getelementptr inbounds [4104 x i32], ptr %551, i64 0, i64 %553, !dbg !1738
  %555 = load i32, ptr %554, align 4, !dbg !1738
  %556 = trunc i32 %555 to i16, !dbg !1738
  %557 = load i32, ptr %23, align 4, !dbg !1741
  %558 = sext i32 %557 to i64, !dbg !1742
  %559 = getelementptr inbounds [4 x i16], ptr %21, i64 0, i64 %558, !dbg !1742
  store i16 %556, ptr %559, align 2, !dbg !1743
  br label %560, !dbg !1742

560:                                              ; preds = %548
  %561 = load i32, ptr %23, align 4, !dbg !1744
  %562 = add nsw i32 %561, 1, !dbg !1744
  store i32 %562, ptr %23, align 4, !dbg !1744
  br label %545, !dbg !1745, !llvm.loop !1746

563:                                              ; preds = %545
  br label %564, !dbg !1748

564:                                              ; preds = %563, %539
  call void @llvm.dbg.declare(metadata ptr %24, metadata !1749, metadata !DIExpression()), !dbg !1750
  %565 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %566 = getelementptr inbounds %struct.libraw_data_t, ptr %565, i32 0, i32 1, !dbg !1751
  %567 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %566, i32 0, i32 2, !dbg !1751
  %568 = load i16, ptr %567, align 4, !dbg !1751
  %569 = zext i16 %568 to i32, !dbg !1751
  %570 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %571 = getelementptr inbounds %struct.libraw_data_t, ptr %570, i32 0, i32 1, !dbg !1751
  %572 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %571, i32 0, i32 0, !dbg !1751
  %573 = load i16, ptr %572, align 8, !dbg !1751
  %574 = zext i16 %573 to i32, !dbg !1751
  %575 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %576 = getelementptr inbounds %struct.libraw_data_t, ptr %575, i32 0, i32 1, !dbg !1751
  %577 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %576, i32 0, i32 4, !dbg !1751
  %578 = load i16, ptr %577, align 8, !dbg !1751
  %579 = zext i16 %578 to i32, !dbg !1751
  %580 = sub nsw i32 %574, %579, !dbg !1751
  %581 = icmp slt i32 %569, %580, !dbg !1751
  br i1 %581, label %582, label %588, !dbg !1751

582:                                              ; preds = %564
  %583 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %584 = getelementptr inbounds %struct.libraw_data_t, ptr %583, i32 0, i32 1, !dbg !1751
  %585 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %584, i32 0, i32 2, !dbg !1751
  %586 = load i16, ptr %585, align 4, !dbg !1751
  %587 = zext i16 %586 to i32, !dbg !1751
  br label %600, !dbg !1751

588:                                              ; preds = %564
  %589 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %590 = getelementptr inbounds %struct.libraw_data_t, ptr %589, i32 0, i32 1, !dbg !1751
  %591 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %590, i32 0, i32 0, !dbg !1751
  %592 = load i16, ptr %591, align 8, !dbg !1751
  %593 = zext i16 %592 to i32, !dbg !1751
  %594 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %595 = getelementptr inbounds %struct.libraw_data_t, ptr %594, i32 0, i32 1, !dbg !1751
  %596 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %595, i32 0, i32 4, !dbg !1751
  %597 = load i16, ptr %596, align 8, !dbg !1751
  %598 = zext i16 %597 to i32, !dbg !1751
  %599 = sub nsw i32 %593, %598, !dbg !1751
  br label %600, !dbg !1751

600:                                              ; preds = %588, %582
  %601 = phi i32 [ %587, %582 ], [ %599, %588 ], !dbg !1751
  %602 = icmp sgt i32 0, %601, !dbg !1751
  br i1 %602, label %603, label %604, !dbg !1751

603:                                              ; preds = %600
  br label %642, !dbg !1751

604:                                              ; preds = %600
  %605 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %606 = getelementptr inbounds %struct.libraw_data_t, ptr %605, i32 0, i32 1, !dbg !1751
  %607 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %606, i32 0, i32 2, !dbg !1751
  %608 = load i16, ptr %607, align 4, !dbg !1751
  %609 = zext i16 %608 to i32, !dbg !1751
  %610 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %611 = getelementptr inbounds %struct.libraw_data_t, ptr %610, i32 0, i32 1, !dbg !1751
  %612 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %611, i32 0, i32 0, !dbg !1751
  %613 = load i16, ptr %612, align 8, !dbg !1751
  %614 = zext i16 %613 to i32, !dbg !1751
  %615 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %616 = getelementptr inbounds %struct.libraw_data_t, ptr %615, i32 0, i32 1, !dbg !1751
  %617 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %616, i32 0, i32 4, !dbg !1751
  %618 = load i16, ptr %617, align 8, !dbg !1751
  %619 = zext i16 %618 to i32, !dbg !1751
  %620 = sub nsw i32 %614, %619, !dbg !1751
  %621 = icmp slt i32 %609, %620, !dbg !1751
  br i1 %621, label %622, label %628, !dbg !1751

622:                                              ; preds = %604
  %623 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %624 = getelementptr inbounds %struct.libraw_data_t, ptr %623, i32 0, i32 1, !dbg !1751
  %625 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %624, i32 0, i32 2, !dbg !1751
  %626 = load i16, ptr %625, align 4, !dbg !1751
  %627 = zext i16 %626 to i32, !dbg !1751
  br label %640, !dbg !1751

628:                                              ; preds = %604
  %629 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %630 = getelementptr inbounds %struct.libraw_data_t, ptr %629, i32 0, i32 1, !dbg !1751
  %631 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %630, i32 0, i32 0, !dbg !1751
  %632 = load i16, ptr %631, align 8, !dbg !1751
  %633 = zext i16 %632 to i32, !dbg !1751
  %634 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1751
  %635 = getelementptr inbounds %struct.libraw_data_t, ptr %634, i32 0, i32 1, !dbg !1751
  %636 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %635, i32 0, i32 4, !dbg !1751
  %637 = load i16, ptr %636, align 8, !dbg !1751
  %638 = zext i16 %637 to i32, !dbg !1751
  %639 = sub nsw i32 %633, %638, !dbg !1751
  br label %640, !dbg !1751

640:                                              ; preds = %628, %622
  %641 = phi i32 [ %627, %622 ], [ %639, %628 ], !dbg !1751
  br label %642, !dbg !1751

642:                                              ; preds = %640, %603
  %643 = phi i32 [ 0, %603 ], [ %641, %640 ], !dbg !1751
  store i32 %643, ptr %24, align 4, !dbg !1750
  call void @llvm.dbg.declare(metadata ptr %25, metadata !1752, metadata !DIExpression()), !dbg !1753
  %644 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %645 = getelementptr inbounds %struct.libraw_data_t, ptr %644, i32 0, i32 1, !dbg !1754
  %646 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %645, i32 0, i32 3, !dbg !1754
  %647 = load i16, ptr %646, align 2, !dbg !1754
  %648 = zext i16 %647 to i32, !dbg !1754
  %649 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %650 = getelementptr inbounds %struct.libraw_data_t, ptr %649, i32 0, i32 1, !dbg !1754
  %651 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %650, i32 0, i32 1, !dbg !1754
  %652 = load i16, ptr %651, align 2, !dbg !1754
  %653 = zext i16 %652 to i32, !dbg !1754
  %654 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %655 = getelementptr inbounds %struct.libraw_data_t, ptr %654, i32 0, i32 1, !dbg !1754
  %656 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %655, i32 0, i32 5, !dbg !1754
  %657 = load i16, ptr %656, align 2, !dbg !1754
  %658 = zext i16 %657 to i32, !dbg !1754
  %659 = sub nsw i32 %653, %658, !dbg !1754
  %660 = icmp slt i32 %648, %659, !dbg !1754
  br i1 %660, label %661, label %667, !dbg !1754

661:                                              ; preds = %642
  %662 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %663 = getelementptr inbounds %struct.libraw_data_t, ptr %662, i32 0, i32 1, !dbg !1754
  %664 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %663, i32 0, i32 3, !dbg !1754
  %665 = load i16, ptr %664, align 2, !dbg !1754
  %666 = zext i16 %665 to i32, !dbg !1754
  br label %679, !dbg !1754

667:                                              ; preds = %642
  %668 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %669 = getelementptr inbounds %struct.libraw_data_t, ptr %668, i32 0, i32 1, !dbg !1754
  %670 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %669, i32 0, i32 1, !dbg !1754
  %671 = load i16, ptr %670, align 2, !dbg !1754
  %672 = zext i16 %671 to i32, !dbg !1754
  %673 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %674 = getelementptr inbounds %struct.libraw_data_t, ptr %673, i32 0, i32 1, !dbg !1754
  %675 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %674, i32 0, i32 5, !dbg !1754
  %676 = load i16, ptr %675, align 2, !dbg !1754
  %677 = zext i16 %676 to i32, !dbg !1754
  %678 = sub nsw i32 %672, %677, !dbg !1754
  br label %679, !dbg !1754

679:                                              ; preds = %667, %661
  %680 = phi i32 [ %666, %661 ], [ %678, %667 ], !dbg !1754
  %681 = icmp sgt i32 0, %680, !dbg !1754
  br i1 %681, label %682, label %683, !dbg !1754

682:                                              ; preds = %679
  br label %721, !dbg !1754

683:                                              ; preds = %679
  %684 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %685 = getelementptr inbounds %struct.libraw_data_t, ptr %684, i32 0, i32 1, !dbg !1754
  %686 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %685, i32 0, i32 3, !dbg !1754
  %687 = load i16, ptr %686, align 2, !dbg !1754
  %688 = zext i16 %687 to i32, !dbg !1754
  %689 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %690 = getelementptr inbounds %struct.libraw_data_t, ptr %689, i32 0, i32 1, !dbg !1754
  %691 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %690, i32 0, i32 1, !dbg !1754
  %692 = load i16, ptr %691, align 2, !dbg !1754
  %693 = zext i16 %692 to i32, !dbg !1754
  %694 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %695 = getelementptr inbounds %struct.libraw_data_t, ptr %694, i32 0, i32 1, !dbg !1754
  %696 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %695, i32 0, i32 5, !dbg !1754
  %697 = load i16, ptr %696, align 2, !dbg !1754
  %698 = zext i16 %697 to i32, !dbg !1754
  %699 = sub nsw i32 %693, %698, !dbg !1754
  %700 = icmp slt i32 %688, %699, !dbg !1754
  br i1 %700, label %701, label %707, !dbg !1754

701:                                              ; preds = %683
  %702 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %703 = getelementptr inbounds %struct.libraw_data_t, ptr %702, i32 0, i32 1, !dbg !1754
  %704 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %703, i32 0, i32 3, !dbg !1754
  %705 = load i16, ptr %704, align 2, !dbg !1754
  %706 = zext i16 %705 to i32, !dbg !1754
  br label %719, !dbg !1754

707:                                              ; preds = %683
  %708 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %709 = getelementptr inbounds %struct.libraw_data_t, ptr %708, i32 0, i32 1, !dbg !1754
  %710 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %709, i32 0, i32 1, !dbg !1754
  %711 = load i16, ptr %710, align 2, !dbg !1754
  %712 = zext i16 %711 to i32, !dbg !1754
  %713 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1754
  %714 = getelementptr inbounds %struct.libraw_data_t, ptr %713, i32 0, i32 1, !dbg !1754
  %715 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %714, i32 0, i32 5, !dbg !1754
  %716 = load i16, ptr %715, align 2, !dbg !1754
  %717 = zext i16 %716 to i32, !dbg !1754
  %718 = sub nsw i32 %712, %717, !dbg !1754
  br label %719, !dbg !1754

719:                                              ; preds = %707, %701
  %720 = phi i32 [ %706, %701 ], [ %718, %707 ], !dbg !1754
  br label %721, !dbg !1754

721:                                              ; preds = %719, %682
  %722 = phi i32 [ 0, %682 ], [ %720, %719 ], !dbg !1754
  store i32 %722, ptr %25, align 4, !dbg !1753
  %723 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1755
  %724 = getelementptr inbounds %struct.libraw_data_t, ptr %723, i32 0, i32 2, !dbg !1757
  %725 = getelementptr inbounds %struct.libraw_iparams_t, ptr %724, i32 0, i32 11, !dbg !1758
  %726 = load i32, ptr %725, align 8, !dbg !1758
  %727 = icmp ne i32 %726, 0, !dbg !1755
  br i1 %727, label %734, label %728, !dbg !1759

728:                                              ; preds = %721
  %729 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1760
  %730 = getelementptr inbounds %struct.libraw_data_t, ptr %729, i32 0, i32 2, !dbg !1760
  %731 = getelementptr inbounds %struct.libraw_iparams_t, ptr %730, i32 0, i32 10, !dbg !1761
  %732 = load i32, ptr %731, align 4, !dbg !1761
  %733 = icmp eq i32 %732, 1, !dbg !1762
  br i1 %733, label %734, label %1018, !dbg !1763

734:                                              ; preds = %728, %721
  %735 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1764
  %736 = getelementptr inbounds %struct.libraw_data_t, ptr %735, i32 0, i32 14, !dbg !1765
  %737 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %736, i32 0, i32 1, !dbg !1766
  %738 = load ptr, ptr %737, align 8, !dbg !1766
  %739 = icmp ne ptr %738, null, !dbg !1764
  br i1 %739, label %740, label %1018, !dbg !1767

740:                                              ; preds = %734
  %741 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1768
  %742 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %741, i32 0, i32 1, !dbg !1768
  %743 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %742, i32 0, i32 4, !dbg !1771
  %744 = load i16, ptr %743, align 2, !dbg !1771
  %745 = icmp ne i16 %744, 0, !dbg !1768
  br i1 %745, label %746, label %1010, !dbg !1772

746:                                              ; preds = %740
  %747 = load i32, ptr %9, align 4, !dbg !1773
  %748 = icmp ne i32 %747, 0, !dbg !1773
  br i1 %748, label %749, label %1002, !dbg !1776

749:                                              ; preds = %746
  %750 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1777
  %751 = getelementptr inbounds %struct.libraw_data_t, ptr %750, i32 0, i32 1, !dbg !1777
  %752 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %751, i32 0, i32 3, !dbg !1779
  %753 = load i16, ptr %752, align 2, !dbg !1779
  %754 = zext i16 %753 to i32, !dbg !1777
  %755 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1780
  %756 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %755, i32 0, i32 4, !dbg !1781
  %757 = getelementptr inbounds %struct.unpacker_data_t, ptr %756, i32 0, i32 16, !dbg !1782
  %758 = load i32, ptr %757, align 8, !dbg !1782
  %759 = icmp ne i32 %758, 0, !dbg !1780
  %760 = xor i1 %759, true, !dbg !1783
  %761 = zext i1 %760 to i32, !dbg !1783
  %762 = ashr i32 %754, %761, !dbg !1784
  %763 = trunc i32 %762 to i16, !dbg !1777
  %764 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1785
  %765 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %764, i32 0, i32 1, !dbg !1785
  %766 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %765, i32 0, i32 4, !dbg !1786
  store i16 %763, ptr %766, align 2, !dbg !1787
  call void @llvm.dbg.declare(metadata ptr %26, metadata !1788, metadata !DIExpression()), !dbg !1789
  %767 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1790
  %768 = getelementptr inbounds %struct.libraw_data_t, ptr %767, i32 0, i32 1, !dbg !1790
  %769 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %768, i32 0, i32 2, !dbg !1791
  %770 = load i16, ptr %769, align 4, !dbg !1791
  %771 = zext i16 %770 to i32, !dbg !1790
  %772 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1792
  %773 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %772, i32 0, i32 4, !dbg !1793
  %774 = getelementptr inbounds %struct.unpacker_data_t, ptr %773, i32 0, i32 16, !dbg !1794
  %775 = load i32, ptr %774, align 8, !dbg !1794
  %776 = ashr i32 %771, %775, !dbg !1795
  %777 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1796
  %778 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %777, i32 0, i32 1, !dbg !1796
  %779 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %778, i32 0, i32 4, !dbg !1797
  %780 = load i16, ptr %779, align 2, !dbg !1797
  %781 = zext i16 %780 to i32, !dbg !1796
  %782 = add nsw i32 %776, %781, !dbg !1798
  store i32 %782, ptr %26, align 4, !dbg !1789
  call void @llvm.dbg.declare(metadata ptr %27, metadata !1799, metadata !DIExpression()), !dbg !1800
  %783 = load i32, ptr %26, align 4, !dbg !1801
  %784 = sub nsw i32 %783, 1, !dbg !1802
  store i32 %784, ptr %27, align 4, !dbg !1800
  call void @llvm.dbg.declare(metadata ptr %28, metadata !1803, metadata !DIExpression()), !dbg !1804
  call void @llvm.dbg.declare(metadata ptr %29, metadata !1805, metadata !DIExpression()), !dbg !1806
  store i32 0, ptr %28, align 4, !dbg !1807
  br label %785, !dbg !1809

785:                                              ; preds = %933, %749
  %786 = load i32, ptr %28, align 4, !dbg !1810
  %787 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1812
  %788 = getelementptr inbounds %struct.libraw_data_t, ptr %787, i32 0, i32 1, !dbg !1812
  %789 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %788, i32 0, i32 2, !dbg !1813
  %790 = load i16, ptr %789, align 4, !dbg !1813
  %791 = zext i16 %790 to i32, !dbg !1812
  %792 = icmp slt i32 %786, %791, !dbg !1814
  br i1 %792, label %793, label %936, !dbg !1815

793:                                              ; preds = %785
  store i32 0, ptr %29, align 4, !dbg !1816
  br label %794, !dbg !1819

794:                                              ; preds = %929, %793
  %795 = load i32, ptr %29, align 4, !dbg !1820
  %796 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1822
  %797 = getelementptr inbounds %struct.libraw_data_t, ptr %796, i32 0, i32 1, !dbg !1822
  %798 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %797, i32 0, i32 3, !dbg !1823
  %799 = load i16, ptr %798, align 2, !dbg !1823
  %800 = zext i16 %799 to i32, !dbg !1822
  %801 = icmp slt i32 %795, %800, !dbg !1824
  br i1 %801, label %802, label %932, !dbg !1825

802:                                              ; preds = %794
  call void @llvm.dbg.declare(metadata ptr %30, metadata !1826, metadata !DIExpression()), !dbg !1828
  call void @llvm.dbg.declare(metadata ptr %31, metadata !1829, metadata !DIExpression()), !dbg !1830
  %803 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1831
  %804 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %803, i32 0, i32 4, !dbg !1833
  %805 = getelementptr inbounds %struct.unpacker_data_t, ptr %804, i32 0, i32 16, !dbg !1834
  %806 = load i32, ptr %805, align 8, !dbg !1834
  %807 = icmp ne i32 %806, 0, !dbg !1831
  br i1 %807, label %808, label %825, !dbg !1835

808:                                              ; preds = %802
  %809 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1836
  %810 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %809, i32 0, i32 1, !dbg !1836
  %811 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %810, i32 0, i32 4, !dbg !1838
  %812 = load i16, ptr %811, align 2, !dbg !1838
  %813 = zext i16 %812 to i32, !dbg !1836
  %814 = sub nsw i32 %813, 1, !dbg !1839
  %815 = load i32, ptr %29, align 4, !dbg !1840
  %816 = sub nsw i32 %814, %815, !dbg !1841
  %817 = load i32, ptr %28, align 4, !dbg !1842
  %818 = ashr i32 %817, 1, !dbg !1843
  %819 = add nsw i32 %816, %818, !dbg !1844
  store i32 %819, ptr %30, align 4, !dbg !1845
  %820 = load i32, ptr %29, align 4, !dbg !1846
  %821 = load i32, ptr %28, align 4, !dbg !1847
  %822 = add nsw i32 %821, 1, !dbg !1848
  %823 = ashr i32 %822, 1, !dbg !1849
  %824 = add nsw i32 %820, %823, !dbg !1850
  store i32 %824, ptr %31, align 4, !dbg !1851
  br label %842, !dbg !1852

825:                                              ; preds = %802
  %826 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1853
  %827 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %826, i32 0, i32 1, !dbg !1853
  %828 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %827, i32 0, i32 4, !dbg !1855
  %829 = load i16, ptr %828, align 2, !dbg !1855
  %830 = zext i16 %829 to i32, !dbg !1853
  %831 = sub nsw i32 %830, 1, !dbg !1856
  %832 = load i32, ptr %28, align 4, !dbg !1857
  %833 = add nsw i32 %831, %832, !dbg !1858
  %834 = load i32, ptr %29, align 4, !dbg !1859
  %835 = ashr i32 %834, 1, !dbg !1860
  %836 = sub nsw i32 %833, %835, !dbg !1861
  store i32 %836, ptr %30, align 4, !dbg !1862
  %837 = load i32, ptr %28, align 4, !dbg !1863
  %838 = load i32, ptr %29, align 4, !dbg !1864
  %839 = add nsw i32 %838, 1, !dbg !1865
  %840 = ashr i32 %839, 1, !dbg !1866
  %841 = add nsw i32 %837, %840, !dbg !1867
  store i32 %841, ptr %31, align 4, !dbg !1868
  br label %842

842:                                              ; preds = %825, %808
  call void @llvm.dbg.declare(metadata ptr %32, metadata !1869, metadata !DIExpression()), !dbg !1870
  %843 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1871
  %844 = getelementptr inbounds %struct.libraw_data_t, ptr %843, i32 0, i32 14, !dbg !1872
  %845 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %844, i32 0, i32 1, !dbg !1873
  %846 = load ptr, ptr %845, align 8, !dbg !1873
  %847 = load i32, ptr %28, align 4, !dbg !1874
  %848 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1875
  %849 = getelementptr inbounds %struct.libraw_data_t, ptr %848, i32 0, i32 1, !dbg !1875
  %850 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %849, i32 0, i32 4, !dbg !1876
  %851 = load i16, ptr %850, align 8, !dbg !1876
  %852 = zext i16 %851 to i32, !dbg !1875
  %853 = add nsw i32 %847, %852, !dbg !1877
  %854 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1878
  %855 = getelementptr inbounds %struct.libraw_data_t, ptr %854, i32 0, i32 1, !dbg !1878
  %856 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %855, i32 0, i32 8, !dbg !1879
  %857 = load i32, ptr %856, align 8, !dbg !1879
  %858 = mul i32 %853, %857, !dbg !1880
  %859 = udiv i32 %858, 2, !dbg !1881
  %860 = load i32, ptr %29, align 4, !dbg !1882
  %861 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1883
  %862 = getelementptr inbounds %struct.libraw_data_t, ptr %861, i32 0, i32 1, !dbg !1883
  %863 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %862, i32 0, i32 5, !dbg !1884
  %864 = load i16, ptr %863, align 2, !dbg !1884
  %865 = zext i16 %864 to i32, !dbg !1883
  %866 = add nsw i32 %860, %865, !dbg !1885
  %867 = add i32 %859, %866, !dbg !1886
  %868 = zext i32 %867 to i64, !dbg !1871
  %869 = getelementptr inbounds i16, ptr %846, i64 %868, !dbg !1871
  %870 = load i16, ptr %869, align 2, !dbg !1871
  store i16 %870, ptr %32, align 2, !dbg !1870
  call void @llvm.dbg.declare(metadata ptr %33, metadata !1887, metadata !DIExpression()), !dbg !1888
  %871 = load i32, ptr %28, align 4, !dbg !1889
  %872 = load i32, ptr %29, align 4, !dbg !1890
  %873 = invoke noundef i32 @_ZN6LibRaw3FCFEii(ptr noundef nonnull align 8 dereferenceable(767320) %43, i32 noundef %871, i32 noundef %872)
          to label %874 unwind label %84, !dbg !1891

874:                                              ; preds = %842
  store i32 %873, ptr %33, align 4, !dbg !1888
  %875 = load i16, ptr %32, align 2, !dbg !1892
  %876 = zext i16 %875 to i32, !dbg !1892
  %877 = load i32, ptr %33, align 4, !dbg !1894
  %878 = sext i32 %877 to i64, !dbg !1895
  %879 = getelementptr inbounds [4 x i16], ptr %21, i64 0, i64 %878, !dbg !1895
  %880 = load i16, ptr %879, align 2, !dbg !1895
  %881 = zext i16 %880 to i32, !dbg !1895
  %882 = icmp sgt i32 %876, %881, !dbg !1896
  br i1 %882, label %883, label %901, !dbg !1897

883:                                              ; preds = %874
  %884 = load i32, ptr %33, align 4, !dbg !1898
  %885 = sext i32 %884 to i64, !dbg !1900
  %886 = getelementptr inbounds [4 x i16], ptr %21, i64 0, i64 %885, !dbg !1900
  %887 = load i16, ptr %886, align 2, !dbg !1900
  %888 = zext i16 %887 to i32, !dbg !1900
  %889 = load i16, ptr %32, align 2, !dbg !1901
  %890 = zext i16 %889 to i32, !dbg !1901
  %891 = sub nsw i32 %890, %888, !dbg !1901
  %892 = trunc i32 %891 to i16, !dbg !1901
  store i16 %892, ptr %32, align 2, !dbg !1901
  %893 = load i16, ptr %22, align 2, !dbg !1902
  %894 = zext i16 %893 to i32, !dbg !1902
  %895 = load i16, ptr %32, align 2, !dbg !1904
  %896 = zext i16 %895 to i32, !dbg !1904
  %897 = icmp slt i32 %894, %896, !dbg !1905
  br i1 %897, label %898, label %900, !dbg !1906

898:                                              ; preds = %883
  %899 = load i16, ptr %32, align 2, !dbg !1907
  store i16 %899, ptr %22, align 2, !dbg !1908
  br label %900, !dbg !1909

900:                                              ; preds = %898, %883
  br label %902, !dbg !1910

901:                                              ; preds = %874
  store i16 0, ptr %32, align 2, !dbg !1911
  br label %902

902:                                              ; preds = %901, %900
  %903 = load i16, ptr %32, align 2, !dbg !1912
  %904 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1913
  %905 = getelementptr inbounds %struct.libraw_data_t, ptr %904, i32 0, i32 0, !dbg !1914
  %906 = load ptr, ptr %905, align 8, !dbg !1914
  %907 = load i32, ptr %30, align 4, !dbg !1915
  %908 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1916
  %909 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %908, i32 0, i32 1, !dbg !1916
  %910 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %909, i32 0, i32 3, !dbg !1917
  %911 = load i16, ptr %910, align 4, !dbg !1917
  %912 = zext i16 %911 to i32, !dbg !1916
  %913 = ashr i32 %907, %912, !dbg !1918
  %914 = load i32, ptr %14, align 4, !dbg !1919
  %915 = mul nsw i32 %913, %914, !dbg !1920
  %916 = load i32, ptr %31, align 4, !dbg !1921
  %917 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1922
  %918 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %917, i32 0, i32 1, !dbg !1922
  %919 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %918, i32 0, i32 3, !dbg !1923
  %920 = load i16, ptr %919, align 4, !dbg !1923
  %921 = zext i16 %920 to i32, !dbg !1922
  %922 = ashr i32 %916, %921, !dbg !1924
  %923 = add nsw i32 %915, %922, !dbg !1925
  %924 = sext i32 %923 to i64, !dbg !1913
  %925 = getelementptr inbounds [4 x i16], ptr %906, i64 %924, !dbg !1913
  %926 = load i32, ptr %33, align 4, !dbg !1926
  %927 = sext i32 %926 to i64, !dbg !1913
  %928 = getelementptr inbounds [4 x i16], ptr %925, i64 0, i64 %927, !dbg !1913
  store i16 %903, ptr %928, align 2, !dbg !1927
  br label %929, !dbg !1928

929:                                              ; preds = %902
  %930 = load i32, ptr %29, align 4, !dbg !1929
  %931 = add nsw i32 %930, 1, !dbg !1929
  store i32 %931, ptr %29, align 4, !dbg !1929
  br label %794, !dbg !1930, !llvm.loop !1931

932:                                              ; preds = %794
  br label %933, !dbg !1933

933:                                              ; preds = %932
  %934 = load i32, ptr %28, align 4, !dbg !1934
  %935 = add nsw i32 %934, 1, !dbg !1934
  store i32 %935, ptr %28, align 4, !dbg !1934
  br label %785, !dbg !1935, !llvm.loop !1936

936:                                              ; preds = %785
  %937 = load i32, ptr %27, align 4, !dbg !1938
  %938 = trunc i32 %937 to i16, !dbg !1938
  %939 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1939
  %940 = getelementptr inbounds %struct.libraw_data_t, ptr %939, i32 0, i32 1, !dbg !1939
  %941 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %940, i32 0, i32 2, !dbg !1940
  store i16 %938, ptr %941, align 4, !dbg !1941
  %942 = load i32, ptr %26, align 4, !dbg !1942
  %943 = trunc i32 %942 to i16, !dbg !1942
  %944 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1943
  %945 = getelementptr inbounds %struct.libraw_data_t, ptr %944, i32 0, i32 1, !dbg !1943
  %946 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %945, i32 0, i32 3, !dbg !1944
  store i16 %943, ptr %946, align 2, !dbg !1945
  %947 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1946
  %948 = getelementptr inbounds %struct.libraw_data_t, ptr %947, i32 0, i32 1, !dbg !1946
  %949 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %948, i32 0, i32 2, !dbg !1947
  %950 = load i16, ptr %949, align 4, !dbg !1947
  %951 = zext i16 %950 to i32, !dbg !1946
  %952 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1948
  %953 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %952, i32 0, i32 1, !dbg !1948
  %954 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %953, i32 0, i32 3, !dbg !1949
  %955 = load i16, ptr %954, align 4, !dbg !1949
  %956 = zext i16 %955 to i32, !dbg !1948
  %957 = add nsw i32 %951, %956, !dbg !1950
  %958 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1951
  %959 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %958, i32 0, i32 1, !dbg !1951
  %960 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %959, i32 0, i32 3, !dbg !1952
  %961 = load i16, ptr %960, align 4, !dbg !1952
  %962 = zext i16 %961 to i32, !dbg !1951
  %963 = ashr i32 %957, %962, !dbg !1953
  %964 = trunc i32 %963 to i16, !dbg !1954
  %965 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1955
  %966 = getelementptr inbounds %struct.libraw_data_t, ptr %965, i32 0, i32 1, !dbg !1955
  %967 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %966, i32 0, i32 6, !dbg !1956
  store i16 %964, ptr %967, align 4, !dbg !1957
  %968 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1958
  %969 = getelementptr inbounds %struct.libraw_data_t, ptr %968, i32 0, i32 1, !dbg !1958
  %970 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %969, i32 0, i32 3, !dbg !1959
  %971 = load i16, ptr %970, align 2, !dbg !1959
  %972 = zext i16 %971 to i32, !dbg !1958
  %973 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1960
  %974 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %973, i32 0, i32 1, !dbg !1960
  %975 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %974, i32 0, i32 3, !dbg !1961
  %976 = load i16, ptr %975, align 4, !dbg !1961
  %977 = zext i16 %976 to i32, !dbg !1960
  %978 = add nsw i32 %972, %977, !dbg !1962
  %979 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 3, !dbg !1963
  %980 = getelementptr inbounds %struct.libraw_internal_data_t, ptr %979, i32 0, i32 1, !dbg !1963
  %981 = getelementptr inbounds %struct.libraw_internal_output_params_t, ptr %980, i32 0, i32 3, !dbg !1964
  %982 = load i16, ptr %981, align 4, !dbg !1964
  %983 = zext i16 %982 to i32, !dbg !1963
  %984 = ashr i32 %978, %983, !dbg !1965
  %985 = trunc i32 %984 to i16, !dbg !1966
  %986 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1967
  %987 = getelementptr inbounds %struct.libraw_data_t, ptr %986, i32 0, i32 1, !dbg !1967
  %988 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %987, i32 0, i32 7, !dbg !1968
  store i16 %985, ptr %988, align 2, !dbg !1969
  %989 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1970
  %990 = getelementptr inbounds %struct.libraw_data_t, ptr %989, i32 0, i32 1, !dbg !1970
  %991 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %990, i32 0, i32 4, !dbg !1971
  %992 = load i16, ptr %991, align 8, !dbg !1971
  %993 = zext i16 %992 to i32, !dbg !1970
  %994 = mul nsw i32 2, %993, !dbg !1972
  %995 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1973
  %996 = getelementptr inbounds %struct.libraw_data_t, ptr %995, i32 0, i32 1, !dbg !1973
  %997 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %996, i32 0, i32 0, !dbg !1974
  %998 = load i16, ptr %997, align 8, !dbg !1975
  %999 = zext i16 %998 to i32, !dbg !1975
  %1000 = sub nsw i32 %999, %994, !dbg !1975
  %1001 = trunc i32 %1000 to i16, !dbg !1975
  store i16 %1001, ptr %997, align 8, !dbg !1975
  br label %1009, !dbg !1976

1002:                                             ; preds = %746
  %1003 = getelementptr inbounds [4 x i16], ptr %21, i64 0, i64 0, !dbg !1977
  %1004 = bitcast ptr %43 to ptr, !dbg !1979
  %1005 = load ptr, ptr %1004, align 8, !dbg !1979
  %1006 = getelementptr inbounds ptr, ptr %1005, i64 12, !dbg !1979
  %1007 = load ptr, ptr %1006, align 8, !dbg !1979
  invoke void %1007(ptr noundef nonnull align 8 dereferenceable(767320) %43, ptr noundef %1003, ptr noundef %22)
          to label %1008 unwind label %84, !dbg !1979

1008:                                             ; preds = %1002
  br label %1009

1009:                                             ; preds = %1008, %936
  br label %1017, !dbg !1980

1010:                                             ; preds = %740
  %1011 = getelementptr inbounds [4 x i16], ptr %21, i64 0, i64 0, !dbg !1981
  %1012 = bitcast ptr %43 to ptr, !dbg !1983
  %1013 = load ptr, ptr %1012, align 8, !dbg !1983
  %1014 = getelementptr inbounds ptr, ptr %1013, i64 13, !dbg !1983
  %1015 = load ptr, ptr %1014, align 8, !dbg !1983
  invoke void %1015(ptr noundef nonnull align 8 dereferenceable(767320) %43, ptr noundef %1011, ptr noundef %22)
          to label %1016 unwind label %84, !dbg !1983

1016:                                             ; preds = %1010
  br label %1017

1017:                                             ; preds = %1016, %1009
  br label %1217, !dbg !1984

1018:                                             ; preds = %734, %728
  %1019 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1985
  %1020 = getelementptr inbounds %struct.libraw_data_t, ptr %1019, i32 0, i32 14, !dbg !1988
  %1021 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %1020, i32 0, i32 2, !dbg !1989
  %1022 = load ptr, ptr %1021, align 8, !dbg !1989
  %1023 = icmp ne ptr %1022, null, !dbg !1985
  br i1 %1023, label %1024, label %1120, !dbg !1990

1024:                                             ; preds = %1018
  %1025 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1991
  %1026 = getelementptr inbounds %struct.libraw_data_t, ptr %1025, i32 0, i32 1, !dbg !1991
  %1027 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1026, i32 0, i32 8, !dbg !1994
  %1028 = load i32, ptr %1027, align 8, !dbg !1994
  %1029 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !1995
  %1030 = getelementptr inbounds %struct.libraw_data_t, ptr %1029, i32 0, i32 1, !dbg !1995
  %1031 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1030, i32 0, i32 3, !dbg !1996
  %1032 = load i16, ptr %1031, align 2, !dbg !1996
  %1033 = zext i16 %1032 to i32, !dbg !1995
  %1034 = mul i32 %1033, 8, !dbg !1997
  %1035 = icmp ne i32 %1028, %1034, !dbg !1998
  br i1 %1035, label %1048, label %1036, !dbg !1999

1036:                                             ; preds = %1024
  %1037 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2000
  %1038 = getelementptr inbounds %struct.libraw_data_t, ptr %1037, i32 0, i32 1, !dbg !2000
  %1039 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1038, i32 0, i32 2, !dbg !2001
  %1040 = load i16, ptr %1039, align 4, !dbg !2001
  %1041 = zext i16 %1040 to i32, !dbg !2000
  %1042 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2002
  %1043 = getelementptr inbounds %struct.libraw_data_t, ptr %1042, i32 0, i32 1, !dbg !2002
  %1044 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1043, i32 0, i32 0, !dbg !2003
  %1045 = load i16, ptr %1044, align 8, !dbg !2003
  %1046 = zext i16 %1045 to i32, !dbg !2002
  %1047 = icmp ne i32 %1041, %1046, !dbg !2004
  br i1 %1047, label %1048, label %1100, !dbg !2005

1048:                                             ; preds = %1036, %1024
  call void @llvm.dbg.declare(metadata ptr %34, metadata !2006, metadata !DIExpression()), !dbg !2009
  store i32 0, ptr %34, align 4, !dbg !2009
  br label %1049, !dbg !2010

1049:                                             ; preds = %1096, %1048
  %1050 = load i32, ptr %34, align 4, !dbg !2011
  %1051 = load i32, ptr %24, align 4, !dbg !2013
  %1052 = icmp slt i32 %1050, %1051, !dbg !2014
  br i1 %1052, label %1053, label %1099, !dbg !2015

1053:                                             ; preds = %1049
  %1054 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2016
  %1055 = getelementptr inbounds %struct.libraw_data_t, ptr %1054, i32 0, i32 0, !dbg !2017
  %1056 = load ptr, ptr %1055, align 8, !dbg !2017
  %1057 = load i32, ptr %34, align 4, !dbg !2018
  %1058 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2019
  %1059 = getelementptr inbounds %struct.libraw_data_t, ptr %1058, i32 0, i32 1, !dbg !2019
  %1060 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1059, i32 0, i32 3, !dbg !2020
  %1061 = load i16, ptr %1060, align 2, !dbg !2020
  %1062 = zext i16 %1061 to i32, !dbg !2019
  %1063 = mul nsw i32 %1057, %1062, !dbg !2021
  %1064 = sext i32 %1063 to i64, !dbg !2016
  %1065 = getelementptr inbounds [4 x i16], ptr %1056, i64 %1064, !dbg !2016
  %1066 = bitcast ptr %1065 to ptr, !dbg !2022
  %1067 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2023
  %1068 = getelementptr inbounds %struct.libraw_data_t, ptr %1067, i32 0, i32 14, !dbg !2024
  %1069 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %1068, i32 0, i32 2, !dbg !2025
  %1070 = load ptr, ptr %1069, align 8, !dbg !2025
  %1071 = load i32, ptr %34, align 4, !dbg !2026
  %1072 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2027
  %1073 = getelementptr inbounds %struct.libraw_data_t, ptr %1072, i32 0, i32 1, !dbg !2027
  %1074 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1073, i32 0, i32 4, !dbg !2028
  %1075 = load i16, ptr %1074, align 8, !dbg !2028
  %1076 = zext i16 %1075 to i32, !dbg !2027
  %1077 = add nsw i32 %1071, %1076, !dbg !2029
  %1078 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2030
  %1079 = getelementptr inbounds %struct.libraw_data_t, ptr %1078, i32 0, i32 1, !dbg !2030
  %1080 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1079, i32 0, i32 8, !dbg !2031
  %1081 = load i32, ptr %1080, align 8, !dbg !2031
  %1082 = mul i32 %1077, %1081, !dbg !2032
  %1083 = udiv i32 %1082, 8, !dbg !2033
  %1084 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2034
  %1085 = getelementptr inbounds %struct.libraw_data_t, ptr %1084, i32 0, i32 1, !dbg !2034
  %1086 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1085, i32 0, i32 5, !dbg !2035
  %1087 = load i16, ptr %1086, align 2, !dbg !2035
  %1088 = zext i16 %1087 to i32, !dbg !2034
  %1089 = add i32 %1083, %1088, !dbg !2036
  %1090 = zext i32 %1089 to i64, !dbg !2023
  %1091 = getelementptr inbounds [4 x i16], ptr %1070, i64 %1090, !dbg !2023
  %1092 = bitcast ptr %1091 to ptr, !dbg !2022
  %1093 = load i32, ptr %25, align 4, !dbg !2037
  %1094 = sext i32 %1093 to i64, !dbg !2037
  %1095 = mul i64 %1094, 8, !dbg !2038
  call void @llvm.memmove.p0.p0.i64(ptr align 2 %1066, ptr align 2 %1092, i64 %1095, i1 false), !dbg !2022
  br label %1096, !dbg !2022

1096:                                             ; preds = %1053
  %1097 = load i32, ptr %34, align 4, !dbg !2039
  %1098 = add nsw i32 %1097, 1, !dbg !2039
  store i32 %1098, ptr %34, align 4, !dbg !2039
  br label %1049, !dbg !2040, !llvm.loop !2041

1099:                                             ; preds = %1049
  br label %1119, !dbg !2043

1100:                                             ; preds = %1036
  %1101 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2044
  %1102 = getelementptr inbounds %struct.libraw_data_t, ptr %1101, i32 0, i32 0, !dbg !2046
  %1103 = load ptr, ptr %1102, align 8, !dbg !2046
  %1104 = bitcast ptr %1103 to ptr, !dbg !2047
  %1105 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2048
  %1106 = getelementptr inbounds %struct.libraw_data_t, ptr %1105, i32 0, i32 14, !dbg !2049
  %1107 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %1106, i32 0, i32 2, !dbg !2050
  %1108 = load ptr, ptr %1107, align 8, !dbg !2050
  %1109 = bitcast ptr %1108 to ptr, !dbg !2047
  %1110 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2051
  %1111 = getelementptr inbounds %struct.libraw_data_t, ptr %1110, i32 0, i32 1, !dbg !2051
  %1112 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1111, i32 0, i32 3, !dbg !2052
  %1113 = load i16, ptr %1112, align 2, !dbg !2052
  %1114 = zext i16 %1113 to i32, !dbg !2051
  %1115 = load i32, ptr %24, align 4, !dbg !2053
  %1116 = mul nsw i32 %1114, %1115, !dbg !2054
  %1117 = sext i32 %1116 to i64, !dbg !2051
  %1118 = mul i64 %1117, 8, !dbg !2055
  call void @llvm.memmove.p0.p0.i64(ptr align 2 %1104, ptr align 2 %1109, i64 %1118, i1 false), !dbg !2047
  br label %1119

1119:                                             ; preds = %1100, %1099
  br label %1216, !dbg !2056

1120:                                             ; preds = %1018
  %1121 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2057
  %1122 = getelementptr inbounds %struct.libraw_data_t, ptr %1121, i32 0, i32 14, !dbg !2059
  %1123 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %1122, i32 0, i32 3, !dbg !2060
  %1124 = load ptr, ptr %1123, align 8, !dbg !2060
  %1125 = icmp ne ptr %1124, null, !dbg !2057
  br i1 %1125, label %1126, label %1212, !dbg !2061

1126:                                             ; preds = %1120
  call void @llvm.dbg.declare(metadata ptr %35, metadata !2062, metadata !DIExpression()), !dbg !2064
  %1127 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2065
  %1128 = getelementptr inbounds %struct.libraw_data_t, ptr %1127, i32 0, i32 14, !dbg !2066
  %1129 = getelementptr inbounds %struct.libraw_rawdata_t, ptr %1128, i32 0, i32 3, !dbg !2067
  %1130 = load ptr, ptr %1129, align 8, !dbg !2067
  %1131 = bitcast ptr %1130 to ptr, !dbg !2068
  store ptr %1131, ptr %35, align 8, !dbg !2064
  call void @llvm.dbg.declare(metadata ptr %36, metadata !2069, metadata !DIExpression()), !dbg !2071
  store i32 0, ptr %36, align 4, !dbg !2071
  br label %1132, !dbg !2072

1132:                                             ; preds = %1208, %1126
  %1133 = load i32, ptr %36, align 4, !dbg !2073
  %1134 = load i32, ptr %24, align 4, !dbg !2075
  %1135 = icmp slt i32 %1133, %1134, !dbg !2076
  br i1 %1135, label %1136, label %1211, !dbg !2077

1136:                                             ; preds = %1132
  call void @llvm.dbg.declare(metadata ptr %37, metadata !2078, metadata !DIExpression()), !dbg !2080
  %1137 = load ptr, ptr %35, align 8, !dbg !2081
  %1138 = load i32, ptr %36, align 4, !dbg !2082
  %1139 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2083
  %1140 = getelementptr inbounds %struct.libraw_data_t, ptr %1139, i32 0, i32 1, !dbg !2083
  %1141 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1140, i32 0, i32 4, !dbg !2084
  %1142 = load i16, ptr %1141, align 8, !dbg !2084
  %1143 = zext i16 %1142 to i32, !dbg !2083
  %1144 = add nsw i32 %1138, %1143, !dbg !2085
  %1145 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2086
  %1146 = getelementptr inbounds %struct.libraw_data_t, ptr %1145, i32 0, i32 1, !dbg !2086
  %1147 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1146, i32 0, i32 8, !dbg !2087
  %1148 = load i32, ptr %1147, align 8, !dbg !2087
  %1149 = mul i32 %1144, %1148, !dbg !2088
  %1150 = zext i32 %1149 to i64, !dbg !2081
  %1151 = getelementptr inbounds i8, ptr %1137, i64 %1150, !dbg !2081
  %1152 = bitcast ptr %1151 to ptr, !dbg !2089
  store ptr %1152, ptr %37, align 8, !dbg !2080
  call void @llvm.dbg.declare(metadata ptr %38, metadata !2090, metadata !DIExpression()), !dbg !2091
  %1153 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2092
  %1154 = getelementptr inbounds %struct.libraw_data_t, ptr %1153, i32 0, i32 0, !dbg !2093
  %1155 = load ptr, ptr %1154, align 8, !dbg !2093
  %1156 = load i32, ptr %36, align 4, !dbg !2094
  %1157 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2095
  %1158 = getelementptr inbounds %struct.libraw_data_t, ptr %1157, i32 0, i32 1, !dbg !2095
  %1159 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1158, i32 0, i32 3, !dbg !2096
  %1160 = load i16, ptr %1159, align 2, !dbg !2096
  %1161 = zext i16 %1160 to i32, !dbg !2095
  %1162 = mul nsw i32 %1156, %1161, !dbg !2097
  %1163 = sext i32 %1162 to i64, !dbg !2092
  %1164 = getelementptr inbounds [4 x i16], ptr %1155, i64 %1163, !dbg !2092
  store ptr %1164, ptr %38, align 8, !dbg !2091
  call void @llvm.dbg.declare(metadata ptr %39, metadata !2098, metadata !DIExpression()), !dbg !2100
  store i32 0, ptr %39, align 4, !dbg !2100
  br label %1165, !dbg !2101

1165:                                             ; preds = %1204, %1136
  %1166 = load i32, ptr %39, align 4, !dbg !2102
  %1167 = load i32, ptr %25, align 4, !dbg !2104
  %1168 = icmp slt i32 %1166, %1167, !dbg !2105
  br i1 %1168, label %1169, label %1207, !dbg !2106

1169:                                             ; preds = %1165
  call void @llvm.dbg.declare(metadata ptr %40, metadata !2107, metadata !DIExpression()), !dbg !2110
  store i32 0, ptr %40, align 4, !dbg !2110
  br label %1170, !dbg !2111

1170:                                             ; preds = %1195, %1169
  %1171 = load i32, ptr %40, align 4, !dbg !2112
  %1172 = icmp slt i32 %1171, 3, !dbg !2114
  br i1 %1172, label %1173, label %1198, !dbg !2115

1173:                                             ; preds = %1170
  %1174 = load ptr, ptr %37, align 8, !dbg !2116
  %1175 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2117
  %1176 = getelementptr inbounds %struct.libraw_data_t, ptr %1175, i32 0, i32 1, !dbg !2117
  %1177 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1176, i32 0, i32 5, !dbg !2118
  %1178 = load i16, ptr %1177, align 2, !dbg !2118
  %1179 = zext i16 %1178 to i32, !dbg !2117
  %1180 = load i32, ptr %39, align 4, !dbg !2119
  %1181 = add nsw i32 %1179, %1180, !dbg !2120
  %1182 = sext i32 %1181 to i64, !dbg !2116
  %1183 = getelementptr inbounds [3 x i16], ptr %1174, i64 %1182, !dbg !2116
  %1184 = load i32, ptr %40, align 4, !dbg !2121
  %1185 = sext i32 %1184 to i64, !dbg !2116
  %1186 = getelementptr inbounds [3 x i16], ptr %1183, i64 0, i64 %1185, !dbg !2116
  %1187 = load i16, ptr %1186, align 2, !dbg !2116
  %1188 = load ptr, ptr %38, align 8, !dbg !2122
  %1189 = load i32, ptr %39, align 4, !dbg !2123
  %1190 = sext i32 %1189 to i64, !dbg !2122
  %1191 = getelementptr inbounds [4 x i16], ptr %1188, i64 %1190, !dbg !2122
  %1192 = load i32, ptr %40, align 4, !dbg !2124
  %1193 = sext i32 %1192 to i64, !dbg !2122
  %1194 = getelementptr inbounds [4 x i16], ptr %1191, i64 0, i64 %1193, !dbg !2122
  store i16 %1187, ptr %1194, align 2, !dbg !2125
  br label %1195, !dbg !2122

1195:                                             ; preds = %1173
  %1196 = load i32, ptr %40, align 4, !dbg !2126
  %1197 = add nsw i32 %1196, 1, !dbg !2126
  store i32 %1197, ptr %40, align 4, !dbg !2126
  br label %1170, !dbg !2127, !llvm.loop !2128

1198:                                             ; preds = %1170
  %1199 = load ptr, ptr %38, align 8, !dbg !2130
  %1200 = load i32, ptr %39, align 4, !dbg !2131
  %1201 = sext i32 %1200 to i64, !dbg !2130
  %1202 = getelementptr inbounds [4 x i16], ptr %1199, i64 %1201, !dbg !2130
  %1203 = getelementptr inbounds [4 x i16], ptr %1202, i64 0, i64 3, !dbg !2130
  store i16 0, ptr %1203, align 2, !dbg !2132
  br label %1204, !dbg !2133

1204:                                             ; preds = %1198
  %1205 = load i32, ptr %39, align 4, !dbg !2134
  %1206 = add nsw i32 %1205, 1, !dbg !2134
  store i32 %1206, ptr %39, align 4, !dbg !2134
  br label %1165, !dbg !2135, !llvm.loop !2136

1207:                                             ; preds = %1165
  br label %1208, !dbg !2138

1208:                                             ; preds = %1207
  %1209 = load i32, ptr %36, align 4, !dbg !2139
  %1210 = add nsw i32 %1209, 1, !dbg !2139
  store i32 %1210, ptr %36, align 4, !dbg !2139
  br label %1132, !dbg !2140, !llvm.loop !2141

1211:                                             ; preds = %1132
  br label %1215, !dbg !2143

1212:                                             ; preds = %1120
  %1213 = call ptr @__cxa_allocate_exception(i64 4) #8, !dbg !2144
  %1214 = bitcast ptr %1213 to ptr, !dbg !2144
  store i32 2, ptr %1214, align 16, !dbg !2144
  invoke void @__cxa_throw(ptr %1213, ptr @_ZTI17LibRaw_exceptions, ptr null) #9
          to label %1327 unwind label %84, !dbg !2144

1215:                                             ; preds = %1211
  br label %1216

1216:                                             ; preds = %1215, %1119
  br label %1217

1217:                                             ; preds = %1216, %1017
  %1218 = bitcast ptr %43 to ptr, !dbg !2146
  %1219 = load ptr, ptr %1218, align 8, !dbg !2146
  %1220 = getelementptr inbounds ptr, ptr %1219, i64 10, !dbg !2146
  %1221 = load ptr, ptr %1220, align 8, !dbg !2146
  %1222 = invoke noundef i32 %1221(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1223 unwind label %84, !dbg !2146

1223:                                             ; preds = %1217
  %1224 = icmp ne i32 %1222, 0, !dbg !2146
  br i1 %1224, label %1225, label %1227, !dbg !2148

1225:                                             ; preds = %1223
  invoke void @_ZN6LibRaw25phase_one_free_tempbufferEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1226 unwind label %84, !dbg !2149

1226:                                             ; preds = %1225
  br label %1227, !dbg !2151

1227:                                             ; preds = %1226, %1223
  %1228 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 11, !dbg !2152
  %1229 = load { i64, i64 }, ptr %1228, align 8, !dbg !2152
  %1230 = extractvalue { i64, i64 } %1229, 0, !dbg !2154
  %1231 = icmp eq i64 %1230, ptrtoint (ptr @_ZN6LibRaw18canon_600_load_rawEv to i64), !dbg !2154
  %1232 = icmp eq i64 %1230, 0, !dbg !2154
  %1233 = extractvalue { i64, i64 } %1229, 1, !dbg !2154
  %1234 = icmp eq i64 %1233, 0, !dbg !2154
  %1235 = or i1 %1232, %1234, !dbg !2154
  %1236 = and i1 %1231, %1235, !dbg !2154
  br i1 %1236, label %1237, label %1251, !dbg !2155

1237:                                             ; preds = %1227
  %1238 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2156
  %1239 = getelementptr inbounds %struct.libraw_data_t, ptr %1238, i32 0, i32 1, !dbg !2156
  %1240 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1239, i32 0, i32 3, !dbg !2157
  %1241 = load i16, ptr %1240, align 2, !dbg !2157
  %1242 = zext i16 %1241 to i32, !dbg !2156
  %1243 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2158
  %1244 = getelementptr inbounds %struct.libraw_data_t, ptr %1243, i32 0, i32 1, !dbg !2158
  %1245 = getelementptr inbounds %struct.libraw_image_sizes_t, ptr %1244, i32 0, i32 1, !dbg !2159
  %1246 = load i16, ptr %1245, align 2, !dbg !2159
  %1247 = zext i16 %1246 to i32, !dbg !2158
  %1248 = icmp slt i32 %1242, %1247, !dbg !2160
  br i1 %1248, label %1249, label %1251, !dbg !2161

1249:                                             ; preds = %1237
  invoke void @_ZN6LibRaw17canon_600_correctEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1250 unwind label %84, !dbg !2162

1250:                                             ; preds = %1249
  br label %1251, !dbg !2164

1251:                                             ; preds = %1250, %1237, %1227
  %1252 = load i32, ptr %5, align 4, !dbg !2165
  %1253 = icmp ne i32 %1252, 0, !dbg !2165
  br i1 %1253, label %1254, label %1288, !dbg !2167

1254:                                             ; preds = %1251
  %1255 = load i16, ptr %22, align 2, !dbg !2168
  %1256 = zext i16 %1255 to i32, !dbg !2168
  %1257 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2170
  %1258 = getelementptr inbounds %struct.libraw_data_t, ptr %1257, i32 0, i32 10, !dbg !2170
  %1259 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1258, i32 0, i32 3, !dbg !2171
  store i32 %1256, ptr %1259, align 4, !dbg !2172
  %1260 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2173
  %1261 = getelementptr inbounds %struct.libraw_data_t, ptr %1260, i32 0, i32 10, !dbg !2173
  %1262 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1261, i32 0, i32 2, !dbg !2174
  %1263 = load i32, ptr %1262, align 8, !dbg !2174
  %1264 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2175
  %1265 = getelementptr inbounds %struct.libraw_data_t, ptr %1264, i32 0, i32 10, !dbg !2175
  %1266 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1265, i32 0, i32 4, !dbg !2176
  %1267 = load i32, ptr %1266, align 8, !dbg !2177
  %1268 = sub i32 %1267, %1263, !dbg !2177
  store i32 %1268, ptr %1266, align 8, !dbg !2177
  %1269 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2178
  %1270 = getelementptr inbounds %struct.libraw_data_t, ptr %1269, i32 0, i32 10, !dbg !2178
  %1271 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1270, i32 0, i32 1, !dbg !2179
  %1272 = getelementptr inbounds [4104 x i32], ptr %1271, i64 0, i64 3, !dbg !2178
  store i32 0, ptr %1272, align 4, !dbg !2180
  %1273 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2181
  %1274 = getelementptr inbounds %struct.libraw_data_t, ptr %1273, i32 0, i32 10, !dbg !2181
  %1275 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1274, i32 0, i32 1, !dbg !2182
  %1276 = getelementptr inbounds [4104 x i32], ptr %1275, i64 0, i64 2, !dbg !2181
  store i32 0, ptr %1276, align 8, !dbg !2183
  %1277 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2184
  %1278 = getelementptr inbounds %struct.libraw_data_t, ptr %1277, i32 0, i32 10, !dbg !2184
  %1279 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1278, i32 0, i32 1, !dbg !2185
  %1280 = getelementptr inbounds [4104 x i32], ptr %1279, i64 0, i64 1, !dbg !2184
  store i32 0, ptr %1280, align 4, !dbg !2186
  %1281 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2187
  %1282 = getelementptr inbounds %struct.libraw_data_t, ptr %1281, i32 0, i32 10, !dbg !2187
  %1283 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1282, i32 0, i32 1, !dbg !2188
  %1284 = getelementptr inbounds [4104 x i32], ptr %1283, i64 0, i64 0, !dbg !2187
  store i32 0, ptr %1284, align 8, !dbg !2189
  %1285 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2190
  %1286 = getelementptr inbounds %struct.libraw_data_t, ptr %1285, i32 0, i32 10, !dbg !2190
  %1287 = getelementptr inbounds %struct.libraw_colordata_t, ptr %1286, i32 0, i32 2, !dbg !2191
  store i32 0, ptr %1287, align 8, !dbg !2192
  br label %1288, !dbg !2193

1288:                                             ; preds = %1254, %1251
  %1289 = getelementptr inbounds %class.LibRaw, ptr %43, i32 0, i32 1, !dbg !2194
  %1290 = getelementptr inbounds %struct.libraw_data_t, ptr %1289, i32 0, i32 8, !dbg !2195
  store i32 31, ptr %1290, align 8, !dbg !2196
  store i32 0, ptr %3, align 4, !dbg !2197
  br label %1320, !dbg !2197

1291:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1292 unwind label %1293, !dbg !2198

1292:                                             ; preds = %1291
  store i32 -100013, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1293:                                             ; preds = %1311, %1309, %1307, %1305, %1303, %1301, %1299, %1297, %1291
  %1294 = landingpad { ptr, i32 }
          cleanup, !dbg !2200
  %1295 = extractvalue { ptr, i32 } %1294, 0, !dbg !2200
  store ptr %1295, ptr %6, align 8, !dbg !2200
  %1296 = extractvalue { ptr, i32 } %1294, 1, !dbg !2200
  store i32 %1296, ptr %7, align 4, !dbg !2200
  call void @__cxa_end_catch() #8, !dbg !2201
  br label %1322, !dbg !2201

1297:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1298 unwind label %1293, !dbg !2198

1298:                                             ; preds = %1297
  store i32 -100007, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1299:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1300 unwind label %1293, !dbg !2198

1300:                                             ; preds = %1299
  store i32 -100012, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1301:                                             ; preds = %96, %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1302 unwind label %1293, !dbg !2198

1302:                                             ; preds = %1301
  store i32 -100008, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1303:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1304 unwind label %1293, !dbg !2198

1304:                                             ; preds = %1303
  store i32 -100008, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1305:                                             ; preds = %96, %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1306 unwind label %1293, !dbg !2198

1306:                                             ; preds = %1305
  store i32 -100009, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1307:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1308 unwind label %1293, !dbg !2198

1308:                                             ; preds = %1307
  store i32 -100010, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1309:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1310 unwind label %1293, !dbg !2198

1310:                                             ; preds = %1309
  store i32 -100011, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1311:                                             ; preds = %96
  invoke void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320) %43)
          to label %1312 unwind label %1293, !dbg !2198

1312:                                             ; preds = %1311
  store i32 -2, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1313:                                             ; preds = %96
  store i32 -1, ptr %3, align 4, !dbg !2198
  store i32 1, ptr %42, align 4
  br label %1316, !dbg !2198

1314:                                             ; No predecessors!
  br label %1315, !dbg !1383

1315:                                             ; preds = %1314
  store i32 0, ptr %42, align 4, !dbg !2201
  br label %1316, !dbg !2201

1316:                                             ; preds = %1315, %1313, %1312, %1310, %1308, %1306, %1304, %1302, %1300, %1298, %1292
  call void @__cxa_end_catch() #8, !dbg !2201
  %1317 = load i32, ptr %42, align 4
  switch i32 %1317, label %1327 [
    i32 0, label %1318
    i32 1, label %1320
  ]

1318:                                             ; preds = %1316
  br label %1319, !dbg !2201

1319:                                             ; preds = %1318
  call void @llvm.trap(), !dbg !2201
  unreachable, !dbg !2201

1320:                                             ; preds = %1316, %1288, %103, %50
  %1321 = load i32, ptr %3, align 4, !dbg !2202
  ret i32 %1321, !dbg !2202

1322:                                             ; preds = %1293, %88
  %1323 = load ptr, ptr %6, align 8, !dbg !1376
  %1324 = load i32, ptr %7, align 4, !dbg !1376
  %1325 = insertvalue { ptr, i32 } undef, ptr %1323, 0, !dbg !1376
  %1326 = insertvalue { ptr, i32 } %1325, i32 %1324, 1, !dbg !1376
  resume { ptr, i32 } %1326, !dbg !1376

1327:                                             ; preds = %1316, %1212, %300
  unreachable
}

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw7recycleEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw29phase_one_allocate_tempbufferEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw25phase_one_free_tempbufferEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare noundef i32 @_ZN6LibRaw24phase_one_subtract_blackEPtS0_(ptr noundef nonnull align 8 dereferenceable(767320), ptr noundef, ptr noundef) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare noundef ptr @_ZN6LibRaw7reallocEPvm(ptr noundef nonnull align 8 dereferenceable(767320), ptr noundef, i64 noundef) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare noundef ptr @_ZN6LibRaw6callocEmm(ptr noundef nonnull align 8 dereferenceable(767320), i64 noundef, i64 noundef) #2 align 2

; Function Attrs: mustprogress noinline optnone uwtable
declare void @_ZN6LibRaw9adjust_blEv(ptr noundef nonnull align 8 dereferenceable(767320)) #2 align 2

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #1 = { nounwind memory(none) }
attributes #2 = { mustprogress noinline optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { mustprogress noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { cold noreturn nounwind memory(inaccessiblemem: write) }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #7 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #8 = { nounwind }
attributes #9 = { noreturn }

!llvm.dbg.cu = !{!0}
!llvm.ident = !{!1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321, !1321}
!llvm.module.flags = !{!1322, !1323, !1324, !1325, !1326, !1327}

!0 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus_14, file: !1, producer: "Ubuntu clang version 14.0.0-1ubuntu1.1", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !81, imports: !96, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/guswjd/conexa/dataset/CVE-2023-1729/LibRaw/src/preprocessing/raw2image.cpp", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729/build-wllvm/LibRaw", checksumkind: CSK_MD5, checksum: "af802a14478a5835c44eef5ee293f29f")
!2 = !{!3, !11, !46, !66}
!3 = distinct !DICompositeType(tag: DW_TAG_enumeration_type, name: "_Lock_policy", scope: !5, file: !4, line: 49, baseType: !6, size: 32, elements: !7, identifier: "_ZTSN9__gnu_cxx12_Lock_policyE")
!4 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/ext/concurrence.h", directory: "")
!5 = !DINamespace(name: "__gnu_cxx", scope: null)
!6 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!7 = !{!8, !9, !10}
!8 = !DIEnumerator(name: "_S_single", value: 0, isUnsigned: true)
!9 = !DIEnumerator(name: "_S_mutex", value: 1, isUnsigned: true)
!10 = !DIEnumerator(name: "_S_atomic", value: 2, isUnsigned: true)
!11 = distinct !DICompositeType(tag: DW_TAG_enumeration_type, name: "LibRaw_progress", file: !12, line: 716, baseType: !6, size: 32, elements: !13, identifier: "_ZTS15LibRaw_progress")
!12 = !DIFile(filename: "LibRaw/libraw/libraw_const.h", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729", checksumkind: CSK_MD5, checksum: "d32d32f3ba76c0c9f2de41078bc5282e")
!13 = !{!14, !15, !16, !17, !18, !19, !20, !21, !22, !23, !24, !25, !26, !27, !28, !29, !30, !31, !32, !33, !34, !35, !36, !37, !38, !39, !40, !41, !42, !43, !44, !45}
!14 = !DIEnumerator(name: "LIBRAW_PROGRESS_START", value: 0, isUnsigned: true)
!15 = !DIEnumerator(name: "LIBRAW_PROGRESS_OPEN", value: 1, isUnsigned: true)
!16 = !DIEnumerator(name: "LIBRAW_PROGRESS_IDENTIFY", value: 2, isUnsigned: true)
!17 = !DIEnumerator(name: "LIBRAW_PROGRESS_SIZE_ADJUST", value: 4, isUnsigned: true)
!18 = !DIEnumerator(name: "LIBRAW_PROGRESS_LOAD_RAW", value: 8, isUnsigned: true)
!19 = !DIEnumerator(name: "LIBRAW_PROGRESS_RAW2_IMAGE", value: 16, isUnsigned: true)
!20 = !DIEnumerator(name: "LIBRAW_PROGRESS_REMOVE_ZEROES", value: 32, isUnsigned: true)
!21 = !DIEnumerator(name: "LIBRAW_PROGRESS_BAD_PIXELS", value: 64, isUnsigned: true)
!22 = !DIEnumerator(name: "LIBRAW_PROGRESS_DARK_FRAME", value: 128, isUnsigned: true)
!23 = !DIEnumerator(name: "LIBRAW_PROGRESS_FOVEON_INTERPOLATE", value: 256, isUnsigned: true)
!24 = !DIEnumerator(name: "LIBRAW_PROGRESS_SCALE_COLORS", value: 512, isUnsigned: true)
!25 = !DIEnumerator(name: "LIBRAW_PROGRESS_PRE_INTERPOLATE", value: 1024, isUnsigned: true)
!26 = !DIEnumerator(name: "LIBRAW_PROGRESS_INTERPOLATE", value: 2048, isUnsigned: true)
!27 = !DIEnumerator(name: "LIBRAW_PROGRESS_MIX_GREEN", value: 4096, isUnsigned: true)
!28 = !DIEnumerator(name: "LIBRAW_PROGRESS_MEDIAN_FILTER", value: 8192, isUnsigned: true)
!29 = !DIEnumerator(name: "LIBRAW_PROGRESS_HIGHLIGHTS", value: 16384, isUnsigned: true)
!30 = !DIEnumerator(name: "LIBRAW_PROGRESS_FUJI_ROTATE", value: 32768, isUnsigned: true)
!31 = !DIEnumerator(name: "LIBRAW_PROGRESS_FLIP", value: 65536, isUnsigned: true)
!32 = !DIEnumerator(name: "LIBRAW_PROGRESS_APPLY_PROFILE", value: 131072, isUnsigned: true)
!33 = !DIEnumerator(name: "LIBRAW_PROGRESS_CONVERT_RGB", value: 262144, isUnsigned: true)
!34 = !DIEnumerator(name: "LIBRAW_PROGRESS_STRETCH", value: 524288, isUnsigned: true)
!35 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE20", value: 1048576, isUnsigned: true)
!36 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE21", value: 2097152, isUnsigned: true)
!37 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE22", value: 4194304, isUnsigned: true)
!38 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE23", value: 8388608, isUnsigned: true)
!39 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE24", value: 16777216, isUnsigned: true)
!40 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE25", value: 33554432, isUnsigned: true)
!41 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE26", value: 67108864, isUnsigned: true)
!42 = !DIEnumerator(name: "LIBRAW_PROGRESS_STAGE27", value: 134217728, isUnsigned: true)
!43 = !DIEnumerator(name: "LIBRAW_PROGRESS_THUMB_LOAD", value: 268435456, isUnsigned: true)
!44 = !DIEnumerator(name: "LIBRAW_PROGRESS_TRESERVED1", value: 536870912, isUnsigned: true)
!45 = !DIEnumerator(name: "LIBRAW_PROGRESS_TRESERVED2", value: 1073741824, isUnsigned: true)
!46 = distinct !DICompositeType(tag: DW_TAG_enumeration_type, name: "LibRaw_errors", file: !12, line: 755, baseType: !47, size: 32, elements: !48, identifier: "_ZTS13LibRaw_errors")
!47 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!48 = !{!49, !50, !51, !52, !53, !54, !55, !56, !57, !58, !59, !60, !61, !62, !63, !64, !65}
!49 = !DIEnumerator(name: "LIBRAW_SUCCESS", value: 0)
!50 = !DIEnumerator(name: "LIBRAW_UNSPECIFIED_ERROR", value: -1)
!51 = !DIEnumerator(name: "LIBRAW_FILE_UNSUPPORTED", value: -2)
!52 = !DIEnumerator(name: "LIBRAW_REQUEST_FOR_NONEXISTENT_IMAGE", value: -3)
!53 = !DIEnumerator(name: "LIBRAW_OUT_OF_ORDER_CALL", value: -4)
!54 = !DIEnumerator(name: "LIBRAW_NO_THUMBNAIL", value: -5)
!55 = !DIEnumerator(name: "LIBRAW_UNSUPPORTED_THUMBNAIL", value: -6)
!56 = !DIEnumerator(name: "LIBRAW_INPUT_CLOSED", value: -7)
!57 = !DIEnumerator(name: "LIBRAW_NOT_IMPLEMENTED", value: -8)
!58 = !DIEnumerator(name: "LIBRAW_REQUEST_FOR_NONEXISTENT_THUMBNAIL", value: -9)
!59 = !DIEnumerator(name: "LIBRAW_UNSUFFICIENT_MEMORY", value: -100007)
!60 = !DIEnumerator(name: "LIBRAW_DATA_ERROR", value: -100008)
!61 = !DIEnumerator(name: "LIBRAW_IO_ERROR", value: -100009)
!62 = !DIEnumerator(name: "LIBRAW_CANCELLED_BY_CALLBACK", value: -100010)
!63 = !DIEnumerator(name: "LIBRAW_BAD_CROP", value: -100011)
!64 = !DIEnumerator(name: "LIBRAW_TOO_BIG", value: -100012)
!65 = !DIEnumerator(name: "LIBRAW_MEMPOOL_OVERFLOW", value: -100013)
!66 = distinct !DICompositeType(tag: DW_TAG_enumeration_type, name: "LibRaw_exceptions", file: !12, line: 699, baseType: !6, size: 32, elements: !67, identifier: "_ZTS17LibRaw_exceptions")
!67 = !{!68, !69, !70, !71, !72, !73, !74, !75, !76, !77, !78, !79, !80}
!68 = !DIEnumerator(name: "LIBRAW_EXCEPTION_NONE", value: 0, isUnsigned: true)
!69 = !DIEnumerator(name: "LIBRAW_EXCEPTION_ALLOC", value: 1, isUnsigned: true)
!70 = !DIEnumerator(name: "LIBRAW_EXCEPTION_DECODE_RAW", value: 2, isUnsigned: true)
!71 = !DIEnumerator(name: "LIBRAW_EXCEPTION_DECODE_JPEG", value: 3, isUnsigned: true)
!72 = !DIEnumerator(name: "LIBRAW_EXCEPTION_IO_EOF", value: 4, isUnsigned: true)
!73 = !DIEnumerator(name: "LIBRAW_EXCEPTION_IO_CORRUPT", value: 5, isUnsigned: true)
!74 = !DIEnumerator(name: "LIBRAW_EXCEPTION_CANCELLED_BY_CALLBACK", value: 6, isUnsigned: true)
!75 = !DIEnumerator(name: "LIBRAW_EXCEPTION_BAD_CROP", value: 7, isUnsigned: true)
!76 = !DIEnumerator(name: "LIBRAW_EXCEPTION_IO_BADFILE", value: 8, isUnsigned: true)
!77 = !DIEnumerator(name: "LIBRAW_EXCEPTION_DECODE_JPEG2000", value: 9, isUnsigned: true)
!78 = !DIEnumerator(name: "LIBRAW_EXCEPTION_TOOBIG", value: 10, isUnsigned: true)
!79 = !DIEnumerator(name: "LIBRAW_EXCEPTION_MEMPOOL", value: 11, isUnsigned: true)
!80 = !DIEnumerator(name: "LIBRAW_EXCEPTION_UNSUPPORTED_FORMAT", value: 12, isUnsigned: true)
!81 = !{!82, !86, !47, !90, !92, !85}
!82 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !83, size: 64)
!83 = !DIDerivedType(tag: DW_TAG_typedef, name: "ushort", file: !84, line: 104, baseType: !85)
!84 = !DIFile(filename: "LibRaw/libraw/libraw_types.h", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729", checksumkind: CSK_MD5, checksum: "d6a9b0d2455cb87dc9c4bf169712db78")
!85 = !DIBasicType(name: "unsigned short", size: 16, encoding: DW_ATE_unsigned)
!86 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !87, size: 64)
!87 = !DICompositeType(tag: DW_TAG_array_type, baseType: !83, size: 64, elements: !88)
!88 = !{!89}
!89 = !DISubrange(count: 4)
!90 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !91, size: 64)
!91 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!92 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !93, size: 64)
!93 = !DICompositeType(tag: DW_TAG_array_type, baseType: !83, size: 48, elements: !94)
!94 = !{!95}
!95 = !DISubrange(count: 3)
!96 = !{!97, !104, !111, !113, !115, !119, !121, !123, !125, !127, !129, !131, !133, !138, !142, !144, !146, !151, !153, !155, !157, !159, !161, !163, !166, !169, !171, !175, !180, !182, !184, !186, !188, !190, !192, !194, !196, !198, !200, !204, !208, !210, !212, !214, !216, !218, !220, !222, !224, !226, !228, !230, !232, !234, !236, !238, !242, !246, !250, !252, !254, !256, !258, !260, !262, !264, !266, !268, !272, !276, !280, !282, !284, !286, !291, !295, !299, !301, !303, !305, !307, !309, !311, !313, !315, !317, !319, !321, !323, !328, !332, !336, !338, !340, !342, !349, !353, !357, !359, !361, !363, !365, !367, !369, !373, !377, !379, !381, !383, !385, !389, !393, !397, !399, !401, !403, !405, !407, !409, !413, !417, !421, !423, !427, !431, !433, !435, !437, !439, !441, !443, !449, !454, !458, !462, !466, !472, !476, !481, !483, !485, !489, !493, !507, !511, !515, !519, !523, !528, !532, !536, !540, !544, !552, !556, !560, !562, !566, !570, !574, !580, !584, !588, !590, !598, !602, !608, !610, !614, !618, !622, !626, !631, !635, !639, !640, !641, !642, !644, !645, !646, !647, !648, !649, !650, !652, !653, !654, !655, !656, !657, !658, !659, !660, !661, !662, !663, !664, !665, !666, !667, !668, !669, !670, !671, !672, !673, !674, !675, !676, !677, !678, !679, !680, !681, !682, !683, !698, !701, !706, !715, !720, !724, !728, !732, !736, !738, !740, !744, !750, !754, !760, !766, !768, !772, !776, !780, !784, !796, !798, !802, !806, !810, !812, !816, !820, !824, !826, !828, !832, !853, !857, !861, !865, !867, !873, !875, !881, !885, !889, !893, !897, !901, !905, !907, !909, !913, !917, !921, !923, !927, !931, !933, !935, !939, !943, !947, !951, !952, !953, !954, !955, !956, !957, !958, !959, !960, !961, !965, !972, !976, !979, !982, !985, !987, !989, !991, !994, !997, !1000, !1003, !1006, !1008, !1012, !1015, !1018, !1021, !1023, !1025, !1027, !1029, !1032, !1035, !1038, !1041, !1044, !1046, !1050, !1054, !1059, !1063, !1065, !1067, !1069, !1071, !1073, !1075, !1077, !1079, !1081, !1083, !1085, !1087, !1089, !1093, !1099, !1104, !1108, !1110, !1112, !1114, !1116, !1123, !1127, !1131, !1135, !1139, !1143, !1148, !1152, !1154, !1158, !1164, !1168, !1173, !1175, !1177, !1181, !1185, !1187, !1189, !1191, !1193, !1197, !1199, !1201, !1205, !1209, !1213, !1217, !1221, !1225, !1227, !1231, !1235, !1239, !1243, !1245, !1247, !1251, !1255, !1256, !1257, !1258, !1259, !1260, !1266, !1269, !1270, !1272, !1274, !1276, !1278, !1282, !1284, !1286, !1288, !1290, !1292, !1294, !1296, !1298, !1302, !1306, !1308, !1312, !1316, !1318}
!97 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !99, file: !103, line: 52)
!98 = !DINamespace(name: "std", scope: null)
!99 = !DISubprogram(name: "abs", scope: !100, file: !100, line: 848, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!100 = !DIFile(filename: "/usr/include/stdlib.h", directory: "", checksumkind: CSK_MD5, checksum: "02258fad21adf111bb9df9825e61954a")
!101 = !DISubroutineType(types: !102)
!102 = !{!47, !47}
!103 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/bits/std_abs.h", directory: "")
!104 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !105, file: !110, line: 83)
!105 = !DISubprogram(name: "acos", scope: !106, file: !106, line: 53, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!106 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/mathcalls.h", directory: "", checksumkind: CSK_MD5, checksum: "8c6e2d0d2bda65bc5ba1ca02b65383b7")
!107 = !DISubroutineType(types: !108)
!108 = !{!109, !109}
!109 = !DIBasicType(name: "double", size: 64, encoding: DW_ATE_float)
!110 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cmath", directory: "")
!111 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !112, file: !110, line: 102)
!112 = !DISubprogram(name: "asin", scope: !106, file: !106, line: 55, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!113 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !114, file: !110, line: 121)
!114 = !DISubprogram(name: "atan", scope: !106, file: !106, line: 57, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!115 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !116, file: !110, line: 140)
!116 = !DISubprogram(name: "atan2", scope: !106, file: !106, line: 59, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!117 = !DISubroutineType(types: !118)
!118 = !{!109, !109, !109}
!119 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !120, file: !110, line: 161)
!120 = !DISubprogram(name: "ceil", scope: !106, file: !106, line: 159, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!121 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !122, file: !110, line: 180)
!122 = !DISubprogram(name: "cos", scope: !106, file: !106, line: 62, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!123 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !124, file: !110, line: 199)
!124 = !DISubprogram(name: "cosh", scope: !106, file: !106, line: 71, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!125 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !126, file: !110, line: 218)
!126 = !DISubprogram(name: "exp", scope: !106, file: !106, line: 95, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!127 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !128, file: !110, line: 237)
!128 = !DISubprogram(name: "fabs", scope: !106, file: !106, line: 162, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!129 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !130, file: !110, line: 256)
!130 = !DISubprogram(name: "floor", scope: !106, file: !106, line: 165, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!131 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !132, file: !110, line: 275)
!132 = !DISubprogram(name: "fmod", scope: !106, file: !106, line: 168, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!133 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !134, file: !110, line: 296)
!134 = !DISubprogram(name: "frexp", scope: !106, file: !106, line: 98, type: !135, flags: DIFlagPrototyped, spFlags: 0)
!135 = !DISubroutineType(types: !136)
!136 = !{!109, !109, !137}
!137 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !47, size: 64)
!138 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !139, file: !110, line: 315)
!139 = !DISubprogram(name: "ldexp", scope: !106, file: !106, line: 101, type: !140, flags: DIFlagPrototyped, spFlags: 0)
!140 = !DISubroutineType(types: !141)
!141 = !{!109, !109, !47}
!142 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !143, file: !110, line: 334)
!143 = !DISubprogram(name: "log", scope: !106, file: !106, line: 104, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!144 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !145, file: !110, line: 353)
!145 = !DISubprogram(name: "log10", scope: !106, file: !106, line: 107, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!146 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !147, file: !110, line: 372)
!147 = !DISubprogram(name: "modf", scope: !106, file: !106, line: 110, type: !148, flags: DIFlagPrototyped, spFlags: 0)
!148 = !DISubroutineType(types: !149)
!149 = !{!109, !109, !150}
!150 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !109, size: 64)
!151 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !152, file: !110, line: 384)
!152 = !DISubprogram(name: "pow", scope: !106, file: !106, line: 140, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!153 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !154, file: !110, line: 421)
!154 = !DISubprogram(name: "sin", scope: !106, file: !106, line: 64, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!155 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !156, file: !110, line: 440)
!156 = !DISubprogram(name: "sinh", scope: !106, file: !106, line: 73, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!157 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !158, file: !110, line: 459)
!158 = !DISubprogram(name: "sqrt", scope: !106, file: !106, line: 143, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!159 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !160, file: !110, line: 478)
!160 = !DISubprogram(name: "tan", scope: !106, file: !106, line: 66, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!161 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !162, file: !110, line: 497)
!162 = !DISubprogram(name: "tanh", scope: !106, file: !106, line: 75, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!163 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !164, file: !110, line: 1065)
!164 = !DIDerivedType(tag: DW_TAG_typedef, name: "double_t", file: !165, line: 164, baseType: !109)
!165 = !DIFile(filename: "/usr/include/math.h", directory: "", checksumkind: CSK_MD5, checksum: "f3450d1d586f704597de1a1b2bed18f3")
!166 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !167, file: !110, line: 1066)
!167 = !DIDerivedType(tag: DW_TAG_typedef, name: "float_t", file: !165, line: 163, baseType: !168)
!168 = !DIBasicType(name: "float", size: 32, encoding: DW_ATE_float)
!169 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !170, file: !110, line: 1069)
!170 = !DISubprogram(name: "acosh", scope: !106, file: !106, line: 85, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!171 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !172, file: !110, line: 1070)
!172 = !DISubprogram(name: "acoshf", scope: !106, file: !106, line: 85, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!173 = !DISubroutineType(types: !174)
!174 = !{!168, !168}
!175 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !176, file: !110, line: 1071)
!176 = !DISubprogram(name: "acoshl", scope: !106, file: !106, line: 85, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!177 = !DISubroutineType(types: !178)
!178 = !{!179, !179}
!179 = !DIBasicType(name: "long double", size: 128, encoding: DW_ATE_float)
!180 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !181, file: !110, line: 1073)
!181 = !DISubprogram(name: "asinh", scope: !106, file: !106, line: 87, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!182 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !183, file: !110, line: 1074)
!183 = !DISubprogram(name: "asinhf", scope: !106, file: !106, line: 87, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!184 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !185, file: !110, line: 1075)
!185 = !DISubprogram(name: "asinhl", scope: !106, file: !106, line: 87, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!186 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !187, file: !110, line: 1077)
!187 = !DISubprogram(name: "atanh", scope: !106, file: !106, line: 89, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!188 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !189, file: !110, line: 1078)
!189 = !DISubprogram(name: "atanhf", scope: !106, file: !106, line: 89, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!190 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !191, file: !110, line: 1079)
!191 = !DISubprogram(name: "atanhl", scope: !106, file: !106, line: 89, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!192 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !193, file: !110, line: 1081)
!193 = !DISubprogram(name: "cbrt", scope: !106, file: !106, line: 152, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!194 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !195, file: !110, line: 1082)
!195 = !DISubprogram(name: "cbrtf", scope: !106, file: !106, line: 152, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!196 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !197, file: !110, line: 1083)
!197 = !DISubprogram(name: "cbrtl", scope: !106, file: !106, line: 152, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!198 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !199, file: !110, line: 1085)
!199 = !DISubprogram(name: "copysign", scope: !106, file: !106, line: 198, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!200 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !201, file: !110, line: 1086)
!201 = !DISubprogram(name: "copysignf", scope: !106, file: !106, line: 198, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!202 = !DISubroutineType(types: !203)
!203 = !{!168, !168, !168}
!204 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !205, file: !110, line: 1087)
!205 = !DISubprogram(name: "copysignl", scope: !106, file: !106, line: 198, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!206 = !DISubroutineType(types: !207)
!207 = !{!179, !179, !179}
!208 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !209, file: !110, line: 1089)
!209 = !DISubprogram(name: "erf", scope: !106, file: !106, line: 231, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!210 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !211, file: !110, line: 1090)
!211 = !DISubprogram(name: "erff", scope: !106, file: !106, line: 231, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!212 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !213, file: !110, line: 1091)
!213 = !DISubprogram(name: "erfl", scope: !106, file: !106, line: 231, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!214 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !215, file: !110, line: 1093)
!215 = !DISubprogram(name: "erfc", scope: !106, file: !106, line: 232, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!216 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !217, file: !110, line: 1094)
!217 = !DISubprogram(name: "erfcf", scope: !106, file: !106, line: 232, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!218 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !219, file: !110, line: 1095)
!219 = !DISubprogram(name: "erfcl", scope: !106, file: !106, line: 232, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!220 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !221, file: !110, line: 1097)
!221 = !DISubprogram(name: "exp2", scope: !106, file: !106, line: 130, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!222 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !223, file: !110, line: 1098)
!223 = !DISubprogram(name: "exp2f", scope: !106, file: !106, line: 130, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!224 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !225, file: !110, line: 1099)
!225 = !DISubprogram(name: "exp2l", scope: !106, file: !106, line: 130, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!226 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !227, file: !110, line: 1101)
!227 = !DISubprogram(name: "expm1", scope: !106, file: !106, line: 119, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!228 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !229, file: !110, line: 1102)
!229 = !DISubprogram(name: "expm1f", scope: !106, file: !106, line: 119, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!230 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !231, file: !110, line: 1103)
!231 = !DISubprogram(name: "expm1l", scope: !106, file: !106, line: 119, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!232 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !233, file: !110, line: 1105)
!233 = !DISubprogram(name: "fdim", scope: !106, file: !106, line: 329, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!234 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !235, file: !110, line: 1106)
!235 = !DISubprogram(name: "fdimf", scope: !106, file: !106, line: 329, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!236 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !237, file: !110, line: 1107)
!237 = !DISubprogram(name: "fdiml", scope: !106, file: !106, line: 329, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!238 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !239, file: !110, line: 1109)
!239 = !DISubprogram(name: "fma", scope: !106, file: !106, line: 340, type: !240, flags: DIFlagPrototyped, spFlags: 0)
!240 = !DISubroutineType(types: !241)
!241 = !{!109, !109, !109, !109}
!242 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !243, file: !110, line: 1110)
!243 = !DISubprogram(name: "fmaf", scope: !106, file: !106, line: 340, type: !244, flags: DIFlagPrototyped, spFlags: 0)
!244 = !DISubroutineType(types: !245)
!245 = !{!168, !168, !168, !168}
!246 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !247, file: !110, line: 1111)
!247 = !DISubprogram(name: "fmal", scope: !106, file: !106, line: 340, type: !248, flags: DIFlagPrototyped, spFlags: 0)
!248 = !DISubroutineType(types: !249)
!249 = !{!179, !179, !179, !179}
!250 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !251, file: !110, line: 1113)
!251 = !DISubprogram(name: "fmax", scope: !106, file: !106, line: 333, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!252 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !253, file: !110, line: 1114)
!253 = !DISubprogram(name: "fmaxf", scope: !106, file: !106, line: 333, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!254 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !255, file: !110, line: 1115)
!255 = !DISubprogram(name: "fmaxl", scope: !106, file: !106, line: 333, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!256 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !257, file: !110, line: 1117)
!257 = !DISubprogram(name: "fmin", scope: !106, file: !106, line: 336, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!258 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !259, file: !110, line: 1118)
!259 = !DISubprogram(name: "fminf", scope: !106, file: !106, line: 336, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!260 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !261, file: !110, line: 1119)
!261 = !DISubprogram(name: "fminl", scope: !106, file: !106, line: 336, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!262 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !263, file: !110, line: 1121)
!263 = !DISubprogram(name: "hypot", scope: !106, file: !106, line: 147, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!264 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !265, file: !110, line: 1122)
!265 = !DISubprogram(name: "hypotf", scope: !106, file: !106, line: 147, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!266 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !267, file: !110, line: 1123)
!267 = !DISubprogram(name: "hypotl", scope: !106, file: !106, line: 147, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!268 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !269, file: !110, line: 1125)
!269 = !DISubprogram(name: "ilogb", scope: !106, file: !106, line: 283, type: !270, flags: DIFlagPrototyped, spFlags: 0)
!270 = !DISubroutineType(types: !271)
!271 = !{!47, !109}
!272 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !273, file: !110, line: 1126)
!273 = !DISubprogram(name: "ilogbf", scope: !106, file: !106, line: 283, type: !274, flags: DIFlagPrototyped, spFlags: 0)
!274 = !DISubroutineType(types: !275)
!275 = !{!47, !168}
!276 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !277, file: !110, line: 1127)
!277 = !DISubprogram(name: "ilogbl", scope: !106, file: !106, line: 283, type: !278, flags: DIFlagPrototyped, spFlags: 0)
!278 = !DISubroutineType(types: !279)
!279 = !{!47, !179}
!280 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !281, file: !110, line: 1129)
!281 = !DISubprogram(name: "lgamma", scope: !106, file: !106, line: 233, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!282 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !283, file: !110, line: 1130)
!283 = !DISubprogram(name: "lgammaf", scope: !106, file: !106, line: 233, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!284 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !285, file: !110, line: 1131)
!285 = !DISubprogram(name: "lgammal", scope: !106, file: !106, line: 233, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!286 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !287, file: !110, line: 1134)
!287 = !DISubprogram(name: "llrint", scope: !106, file: !106, line: 319, type: !288, flags: DIFlagPrototyped, spFlags: 0)
!288 = !DISubroutineType(types: !289)
!289 = !{!290, !109}
!290 = !DIBasicType(name: "long long", size: 64, encoding: DW_ATE_signed)
!291 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !292, file: !110, line: 1135)
!292 = !DISubprogram(name: "llrintf", scope: !106, file: !106, line: 319, type: !293, flags: DIFlagPrototyped, spFlags: 0)
!293 = !DISubroutineType(types: !294)
!294 = !{!290, !168}
!295 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !296, file: !110, line: 1136)
!296 = !DISubprogram(name: "llrintl", scope: !106, file: !106, line: 319, type: !297, flags: DIFlagPrototyped, spFlags: 0)
!297 = !DISubroutineType(types: !298)
!298 = !{!290, !179}
!299 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !300, file: !110, line: 1138)
!300 = !DISubprogram(name: "llround", scope: !106, file: !106, line: 325, type: !288, flags: DIFlagPrototyped, spFlags: 0)
!301 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !302, file: !110, line: 1139)
!302 = !DISubprogram(name: "llroundf", scope: !106, file: !106, line: 325, type: !293, flags: DIFlagPrototyped, spFlags: 0)
!303 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !304, file: !110, line: 1140)
!304 = !DISubprogram(name: "llroundl", scope: !106, file: !106, line: 325, type: !297, flags: DIFlagPrototyped, spFlags: 0)
!305 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !306, file: !110, line: 1143)
!306 = !DISubprogram(name: "log1p", scope: !106, file: !106, line: 122, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!307 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !308, file: !110, line: 1144)
!308 = !DISubprogram(name: "log1pf", scope: !106, file: !106, line: 122, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!309 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !310, file: !110, line: 1145)
!310 = !DISubprogram(name: "log1pl", scope: !106, file: !106, line: 122, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!311 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !312, file: !110, line: 1147)
!312 = !DISubprogram(name: "log2", scope: !106, file: !106, line: 133, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!313 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !314, file: !110, line: 1148)
!314 = !DISubprogram(name: "log2f", scope: !106, file: !106, line: 133, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!315 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !316, file: !110, line: 1149)
!316 = !DISubprogram(name: "log2l", scope: !106, file: !106, line: 133, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!317 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !318, file: !110, line: 1151)
!318 = !DISubprogram(name: "logb", scope: !106, file: !106, line: 125, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!319 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !320, file: !110, line: 1152)
!320 = !DISubprogram(name: "logbf", scope: !106, file: !106, line: 125, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!321 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !322, file: !110, line: 1153)
!322 = !DISubprogram(name: "logbl", scope: !106, file: !106, line: 125, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!323 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !324, file: !110, line: 1155)
!324 = !DISubprogram(name: "lrint", scope: !106, file: !106, line: 317, type: !325, flags: DIFlagPrototyped, spFlags: 0)
!325 = !DISubroutineType(types: !326)
!326 = !{!327, !109}
!327 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!328 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !329, file: !110, line: 1156)
!329 = !DISubprogram(name: "lrintf", scope: !106, file: !106, line: 317, type: !330, flags: DIFlagPrototyped, spFlags: 0)
!330 = !DISubroutineType(types: !331)
!331 = !{!327, !168}
!332 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !333, file: !110, line: 1157)
!333 = !DISubprogram(name: "lrintl", scope: !106, file: !106, line: 317, type: !334, flags: DIFlagPrototyped, spFlags: 0)
!334 = !DISubroutineType(types: !335)
!335 = !{!327, !179}
!336 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !337, file: !110, line: 1159)
!337 = !DISubprogram(name: "lround", scope: !106, file: !106, line: 323, type: !325, flags: DIFlagPrototyped, spFlags: 0)
!338 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !339, file: !110, line: 1160)
!339 = !DISubprogram(name: "lroundf", scope: !106, file: !106, line: 323, type: !330, flags: DIFlagPrototyped, spFlags: 0)
!340 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !341, file: !110, line: 1161)
!341 = !DISubprogram(name: "lroundl", scope: !106, file: !106, line: 323, type: !334, flags: DIFlagPrototyped, spFlags: 0)
!342 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !343, file: !110, line: 1163)
!343 = !DISubprogram(name: "nan", scope: !106, file: !106, line: 203, type: !344, flags: DIFlagPrototyped, spFlags: 0)
!344 = !DISubroutineType(types: !345)
!345 = !{!109, !346}
!346 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !347, size: 64)
!347 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !348)
!348 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!349 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !350, file: !110, line: 1164)
!350 = !DISubprogram(name: "nanf", scope: !106, file: !106, line: 203, type: !351, flags: DIFlagPrototyped, spFlags: 0)
!351 = !DISubroutineType(types: !352)
!352 = !{!168, !346}
!353 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !354, file: !110, line: 1165)
!354 = !DISubprogram(name: "nanl", scope: !106, file: !106, line: 203, type: !355, flags: DIFlagPrototyped, spFlags: 0)
!355 = !DISubroutineType(types: !356)
!356 = !{!179, !346}
!357 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !358, file: !110, line: 1167)
!358 = !DISubprogram(name: "nearbyint", scope: !106, file: !106, line: 297, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!359 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !360, file: !110, line: 1168)
!360 = !DISubprogram(name: "nearbyintf", scope: !106, file: !106, line: 297, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!361 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !362, file: !110, line: 1169)
!362 = !DISubprogram(name: "nearbyintl", scope: !106, file: !106, line: 297, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!363 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !364, file: !110, line: 1171)
!364 = !DISubprogram(name: "nextafter", scope: !106, file: !106, line: 262, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!365 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !366, file: !110, line: 1172)
!366 = !DISubprogram(name: "nextafterf", scope: !106, file: !106, line: 262, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!367 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !368, file: !110, line: 1173)
!368 = !DISubprogram(name: "nextafterl", scope: !106, file: !106, line: 262, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!369 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !370, file: !110, line: 1175)
!370 = !DISubprogram(name: "nexttoward", scope: !106, file: !106, line: 264, type: !371, flags: DIFlagPrototyped, spFlags: 0)
!371 = !DISubroutineType(types: !372)
!372 = !{!109, !109, !179}
!373 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !374, file: !110, line: 1176)
!374 = !DISubprogram(name: "nexttowardf", scope: !106, file: !106, line: 264, type: !375, flags: DIFlagPrototyped, spFlags: 0)
!375 = !DISubroutineType(types: !376)
!376 = !{!168, !168, !179}
!377 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !378, file: !110, line: 1177)
!378 = !DISubprogram(name: "nexttowardl", scope: !106, file: !106, line: 264, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!379 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !380, file: !110, line: 1179)
!380 = !DISubprogram(name: "remainder", scope: !106, file: !106, line: 275, type: !117, flags: DIFlagPrototyped, spFlags: 0)
!381 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !382, file: !110, line: 1180)
!382 = !DISubprogram(name: "remainderf", scope: !106, file: !106, line: 275, type: !202, flags: DIFlagPrototyped, spFlags: 0)
!383 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !384, file: !110, line: 1181)
!384 = !DISubprogram(name: "remainderl", scope: !106, file: !106, line: 275, type: !206, flags: DIFlagPrototyped, spFlags: 0)
!385 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !386, file: !110, line: 1183)
!386 = !DISubprogram(name: "remquo", scope: !106, file: !106, line: 310, type: !387, flags: DIFlagPrototyped, spFlags: 0)
!387 = !DISubroutineType(types: !388)
!388 = !{!109, !109, !109, !137}
!389 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !390, file: !110, line: 1184)
!390 = !DISubprogram(name: "remquof", scope: !106, file: !106, line: 310, type: !391, flags: DIFlagPrototyped, spFlags: 0)
!391 = !DISubroutineType(types: !392)
!392 = !{!168, !168, !168, !137}
!393 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !394, file: !110, line: 1185)
!394 = !DISubprogram(name: "remquol", scope: !106, file: !106, line: 310, type: !395, flags: DIFlagPrototyped, spFlags: 0)
!395 = !DISubroutineType(types: !396)
!396 = !{!179, !179, !179, !137}
!397 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !398, file: !110, line: 1187)
!398 = !DISubprogram(name: "rint", scope: !106, file: !106, line: 259, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!399 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !400, file: !110, line: 1188)
!400 = !DISubprogram(name: "rintf", scope: !106, file: !106, line: 259, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!401 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !402, file: !110, line: 1189)
!402 = !DISubprogram(name: "rintl", scope: !106, file: !106, line: 259, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!403 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !404, file: !110, line: 1191)
!404 = !DISubprogram(name: "round", scope: !106, file: !106, line: 301, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!405 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !406, file: !110, line: 1192)
!406 = !DISubprogram(name: "roundf", scope: !106, file: !106, line: 301, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!407 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !408, file: !110, line: 1193)
!408 = !DISubprogram(name: "roundl", scope: !106, file: !106, line: 301, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!409 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !410, file: !110, line: 1195)
!410 = !DISubprogram(name: "scalbln", scope: !106, file: !106, line: 293, type: !411, flags: DIFlagPrototyped, spFlags: 0)
!411 = !DISubroutineType(types: !412)
!412 = !{!109, !109, !327}
!413 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !414, file: !110, line: 1196)
!414 = !DISubprogram(name: "scalblnf", scope: !106, file: !106, line: 293, type: !415, flags: DIFlagPrototyped, spFlags: 0)
!415 = !DISubroutineType(types: !416)
!416 = !{!168, !168, !327}
!417 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !418, file: !110, line: 1197)
!418 = !DISubprogram(name: "scalblnl", scope: !106, file: !106, line: 293, type: !419, flags: DIFlagPrototyped, spFlags: 0)
!419 = !DISubroutineType(types: !420)
!420 = !{!179, !179, !327}
!421 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !422, file: !110, line: 1199)
!422 = !DISubprogram(name: "scalbn", scope: !106, file: !106, line: 279, type: !140, flags: DIFlagPrototyped, spFlags: 0)
!423 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !424, file: !110, line: 1200)
!424 = !DISubprogram(name: "scalbnf", scope: !106, file: !106, line: 279, type: !425, flags: DIFlagPrototyped, spFlags: 0)
!425 = !DISubroutineType(types: !426)
!426 = !{!168, !168, !47}
!427 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !428, file: !110, line: 1201)
!428 = !DISubprogram(name: "scalbnl", scope: !106, file: !106, line: 279, type: !429, flags: DIFlagPrototyped, spFlags: 0)
!429 = !DISubroutineType(types: !430)
!430 = !{!179, !179, !47}
!431 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !432, file: !110, line: 1203)
!432 = !DISubprogram(name: "tgamma", scope: !106, file: !106, line: 238, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!433 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !434, file: !110, line: 1204)
!434 = !DISubprogram(name: "tgammaf", scope: !106, file: !106, line: 238, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!435 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !436, file: !110, line: 1205)
!436 = !DISubprogram(name: "tgammal", scope: !106, file: !106, line: 238, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!437 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !438, file: !110, line: 1207)
!438 = !DISubprogram(name: "trunc", scope: !106, file: !106, line: 305, type: !107, flags: DIFlagPrototyped, spFlags: 0)
!439 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !440, file: !110, line: 1208)
!440 = !DISubprogram(name: "truncf", scope: !106, file: !106, line: 305, type: !173, flags: DIFlagPrototyped, spFlags: 0)
!441 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !442, file: !110, line: 1209)
!442 = !DISubprogram(name: "truncl", scope: !106, file: !106, line: 305, type: !177, flags: DIFlagPrototyped, spFlags: 0)
!443 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !444, file: !448, line: 38)
!444 = !DISubprogram(name: "abs", linkageName: "_ZSt3absg", scope: !98, file: !103, line: 103, type: !445, flags: DIFlagPrototyped, spFlags: 0)
!445 = !DISubroutineType(types: !446)
!446 = !{!447, !447}
!447 = !DIBasicType(name: "__float128", size: 128, encoding: DW_ATE_float)
!448 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/math.h", directory: "", checksumkind: CSK_MD5, checksum: "a990cded20a6fb8dad866460b8c40922")
!449 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !450, file: !448, line: 54)
!450 = !DISubprogram(name: "modf", linkageName: "_ZSt4modfePe", scope: !98, file: !110, line: 380, type: !451, flags: DIFlagPrototyped, spFlags: 0)
!451 = !DISubroutineType(types: !452)
!452 = !{!179, !179, !453}
!453 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !179, size: 64)
!454 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !455, file: !456, line: 68)
!455 = distinct !DICompositeType(tag: DW_TAG_class_type, name: "exception_ptr", scope: !457, file: !456, line: 90, size: 64, flags: DIFlagFwdDecl | DIFlagNonTrivial, identifier: "_ZTSNSt15__exception_ptr13exception_ptrE")
!456 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/bits/exception_ptr.h", directory: "", checksumkind: CSK_MD5, checksum: "ed433011c81450fc2dabd9aa8a29a038")
!457 = !DINamespace(name: "__exception_ptr", scope: !98)
!458 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !457, entity: !459, file: !456, line: 84)
!459 = !DISubprogram(name: "rethrow_exception", linkageName: "_ZSt17rethrow_exceptionNSt15__exception_ptr13exception_ptrE", scope: !98, file: !456, line: 80, type: !460, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: 0)
!460 = !DISubroutineType(types: !461)
!461 = !{null, !455}
!462 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !463, file: !465, line: 127)
!463 = !DIDerivedType(tag: DW_TAG_typedef, name: "div_t", file: !100, line: 63, baseType: !464)
!464 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !100, line: 59, size: 64, flags: DIFlagFwdDecl, identifier: "_ZTS5div_t")
!465 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cstdlib", directory: "")
!466 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !467, file: !465, line: 128)
!467 = !DIDerivedType(tag: DW_TAG_typedef, name: "ldiv_t", file: !100, line: 71, baseType: !468)
!468 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !100, line: 67, size: 128, flags: DIFlagTypePassByValue, elements: !469, identifier: "_ZTS6ldiv_t")
!469 = !{!470, !471}
!470 = !DIDerivedType(tag: DW_TAG_member, name: "quot", scope: !468, file: !100, line: 69, baseType: !327, size: 64)
!471 = !DIDerivedType(tag: DW_TAG_member, name: "rem", scope: !468, file: !100, line: 70, baseType: !327, size: 64, offset: 64)
!472 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !473, file: !465, line: 130)
!473 = !DISubprogram(name: "abort", scope: !100, file: !100, line: 598, type: !474, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: 0)
!474 = !DISubroutineType(types: !475)
!475 = !{null}
!476 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !477, file: !465, line: 134)
!477 = !DISubprogram(name: "atexit", scope: !100, file: !100, line: 602, type: !478, flags: DIFlagPrototyped, spFlags: 0)
!478 = !DISubroutineType(types: !479)
!479 = !{!47, !480}
!480 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !474, size: 64)
!481 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !482, file: !465, line: 137)
!482 = !DISubprogram(name: "at_quick_exit", scope: !100, file: !100, line: 607, type: !478, flags: DIFlagPrototyped, spFlags: 0)
!483 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !484, file: !465, line: 140)
!484 = !DISubprogram(name: "atof", scope: !100, file: !100, line: 102, type: !344, flags: DIFlagPrototyped, spFlags: 0)
!485 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !486, file: !465, line: 141)
!486 = !DISubprogram(name: "atoi", scope: !100, file: !100, line: 105, type: !487, flags: DIFlagPrototyped, spFlags: 0)
!487 = !DISubroutineType(types: !488)
!488 = !{!47, !346}
!489 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !490, file: !465, line: 142)
!490 = !DISubprogram(name: "atol", scope: !100, file: !100, line: 108, type: !491, flags: DIFlagPrototyped, spFlags: 0)
!491 = !DISubroutineType(types: !492)
!492 = !{!327, !346}
!493 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !494, file: !465, line: 143)
!494 = !DISubprogram(name: "bsearch", scope: !100, file: !100, line: 828, type: !495, flags: DIFlagPrototyped, spFlags: 0)
!495 = !DISubroutineType(types: !496)
!496 = !{!497, !498, !498, !500, !500, !503}
!497 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!498 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !499, size: 64)
!499 = !DIDerivedType(tag: DW_TAG_const_type, baseType: null)
!500 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !501, line: 46, baseType: !502)
!501 = !DIFile(filename: "/usr/lib/llvm-14/lib/clang/14.0.0/include/stddef.h", directory: "", checksumkind: CSK_MD5, checksum: "2499dd2361b915724b073282bea3a7bc")
!502 = !DIBasicType(name: "unsigned long", size: 64, encoding: DW_ATE_unsigned)
!503 = !DIDerivedType(tag: DW_TAG_typedef, name: "__compar_fn_t", file: !100, line: 816, baseType: !504)
!504 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !505, size: 64)
!505 = !DISubroutineType(types: !506)
!506 = !{!47, !498, !498}
!507 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !508, file: !465, line: 144)
!508 = !DISubprogram(name: "calloc", scope: !100, file: !100, line: 543, type: !509, flags: DIFlagPrototyped, spFlags: 0)
!509 = !DISubroutineType(types: !510)
!510 = !{!497, !500, !500}
!511 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !512, file: !465, line: 145)
!512 = !DISubprogram(name: "div", scope: !100, file: !100, line: 860, type: !513, flags: DIFlagPrototyped, spFlags: 0)
!513 = !DISubroutineType(types: !514)
!514 = !{!463, !47, !47}
!515 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !516, file: !465, line: 146)
!516 = !DISubprogram(name: "exit", scope: !100, file: !100, line: 624, type: !517, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: 0)
!517 = !DISubroutineType(types: !518)
!518 = !{null, !47}
!519 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !520, file: !465, line: 147)
!520 = !DISubprogram(name: "free", scope: !100, file: !100, line: 555, type: !521, flags: DIFlagPrototyped, spFlags: 0)
!521 = !DISubroutineType(types: !522)
!522 = !{null, !497}
!523 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !524, file: !465, line: 148)
!524 = !DISubprogram(name: "getenv", scope: !100, file: !100, line: 641, type: !525, flags: DIFlagPrototyped, spFlags: 0)
!525 = !DISubroutineType(types: !526)
!526 = !{!527, !346}
!527 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !348, size: 64)
!528 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !529, file: !465, line: 149)
!529 = !DISubprogram(name: "labs", scope: !100, file: !100, line: 849, type: !530, flags: DIFlagPrototyped, spFlags: 0)
!530 = !DISubroutineType(types: !531)
!531 = !{!327, !327}
!532 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !533, file: !465, line: 150)
!533 = !DISubprogram(name: "ldiv", scope: !100, file: !100, line: 862, type: !534, flags: DIFlagPrototyped, spFlags: 0)
!534 = !DISubroutineType(types: !535)
!535 = !{!467, !327, !327}
!536 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !537, file: !465, line: 151)
!537 = !DISubprogram(name: "malloc", scope: !100, file: !100, line: 540, type: !538, flags: DIFlagPrototyped, spFlags: 0)
!538 = !DISubroutineType(types: !539)
!539 = !{!497, !500}
!540 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !541, file: !465, line: 153)
!541 = !DISubprogram(name: "mblen", scope: !100, file: !100, line: 930, type: !542, flags: DIFlagPrototyped, spFlags: 0)
!542 = !DISubroutineType(types: !543)
!543 = !{!47, !346, !500}
!544 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !545, file: !465, line: 154)
!545 = !DISubprogram(name: "mbstowcs", scope: !100, file: !100, line: 941, type: !546, flags: DIFlagPrototyped, spFlags: 0)
!546 = !DISubroutineType(types: !547)
!547 = !{!500, !548, !551, !500}
!548 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !549)
!549 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !550, size: 64)
!550 = !DIBasicType(name: "wchar_t", size: 32, encoding: DW_ATE_signed)
!551 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !346)
!552 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !553, file: !465, line: 155)
!553 = !DISubprogram(name: "mbtowc", scope: !100, file: !100, line: 933, type: !554, flags: DIFlagPrototyped, spFlags: 0)
!554 = !DISubroutineType(types: !555)
!555 = !{!47, !548, !551, !500}
!556 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !557, file: !465, line: 157)
!557 = !DISubprogram(name: "qsort", scope: !100, file: !100, line: 838, type: !558, flags: DIFlagPrototyped, spFlags: 0)
!558 = !DISubroutineType(types: !559)
!559 = !{null, !497, !500, !500, !503}
!560 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !561, file: !465, line: 160)
!561 = !DISubprogram(name: "quick_exit", scope: !100, file: !100, line: 630, type: !517, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: 0)
!562 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !563, file: !465, line: 163)
!563 = !DISubprogram(name: "rand", scope: !100, file: !100, line: 454, type: !564, flags: DIFlagPrototyped, spFlags: 0)
!564 = !DISubroutineType(types: !565)
!565 = !{!47}
!566 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !567, file: !465, line: 164)
!567 = !DISubprogram(name: "realloc", scope: !100, file: !100, line: 551, type: !568, flags: DIFlagPrototyped, spFlags: 0)
!568 = !DISubroutineType(types: !569)
!569 = !{!497, !497, !500}
!570 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !571, file: !465, line: 165)
!571 = !DISubprogram(name: "srand", scope: !100, file: !100, line: 456, type: !572, flags: DIFlagPrototyped, spFlags: 0)
!572 = !DISubroutineType(types: !573)
!573 = !{null, !6}
!574 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !575, file: !465, line: 166)
!575 = !DISubprogram(name: "strtod", scope: !100, file: !100, line: 118, type: !576, flags: DIFlagPrototyped, spFlags: 0)
!576 = !DISubroutineType(types: !577)
!577 = !{!109, !551, !578}
!578 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !579)
!579 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !527, size: 64)
!580 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !581, file: !465, line: 167)
!581 = !DISubprogram(name: "strtol", scope: !100, file: !100, line: 177, type: !582, flags: DIFlagPrototyped, spFlags: 0)
!582 = !DISubroutineType(types: !583)
!583 = !{!327, !551, !578, !47}
!584 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !585, file: !465, line: 168)
!585 = !DISubprogram(name: "strtoul", scope: !100, file: !100, line: 181, type: !586, flags: DIFlagPrototyped, spFlags: 0)
!586 = !DISubroutineType(types: !587)
!587 = !{!502, !551, !578, !47}
!588 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !589, file: !465, line: 169)
!589 = !DISubprogram(name: "system", scope: !100, file: !100, line: 791, type: !487, flags: DIFlagPrototyped, spFlags: 0)
!590 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !591, file: !465, line: 171)
!591 = !DISubprogram(name: "wcstombs", scope: !100, file: !100, line: 945, type: !592, flags: DIFlagPrototyped, spFlags: 0)
!592 = !DISubroutineType(types: !593)
!593 = !{!500, !594, !595, !500}
!594 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !527)
!595 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !596)
!596 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !597, size: 64)
!597 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !550)
!598 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !599, file: !465, line: 172)
!599 = !DISubprogram(name: "wctomb", scope: !100, file: !100, line: 937, type: !600, flags: DIFlagPrototyped, spFlags: 0)
!600 = !DISubroutineType(types: !601)
!601 = !{!47, !527, !550}
!602 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !603, file: !465, line: 200)
!603 = !DIDerivedType(tag: DW_TAG_typedef, name: "lldiv_t", file: !100, line: 81, baseType: !604)
!604 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !100, line: 77, size: 128, flags: DIFlagTypePassByValue, elements: !605, identifier: "_ZTS7lldiv_t")
!605 = !{!606, !607}
!606 = !DIDerivedType(tag: DW_TAG_member, name: "quot", scope: !604, file: !100, line: 79, baseType: !290, size: 64)
!607 = !DIDerivedType(tag: DW_TAG_member, name: "rem", scope: !604, file: !100, line: 80, baseType: !290, size: 64, offset: 64)
!608 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !609, file: !465, line: 206)
!609 = !DISubprogram(name: "_Exit", scope: !100, file: !100, line: 636, type: !517, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: 0)
!610 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !611, file: !465, line: 210)
!611 = !DISubprogram(name: "llabs", scope: !100, file: !100, line: 852, type: !612, flags: DIFlagPrototyped, spFlags: 0)
!612 = !DISubroutineType(types: !613)
!613 = !{!290, !290}
!614 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !615, file: !465, line: 216)
!615 = !DISubprogram(name: "lldiv", scope: !100, file: !100, line: 866, type: !616, flags: DIFlagPrototyped, spFlags: 0)
!616 = !DISubroutineType(types: !617)
!617 = !{!603, !290, !290}
!618 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !619, file: !465, line: 227)
!619 = !DISubprogram(name: "atoll", scope: !100, file: !100, line: 113, type: !620, flags: DIFlagPrototyped, spFlags: 0)
!620 = !DISubroutineType(types: !621)
!621 = !{!290, !346}
!622 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !623, file: !465, line: 228)
!623 = !DISubprogram(name: "strtoll", scope: !100, file: !100, line: 201, type: !624, flags: DIFlagPrototyped, spFlags: 0)
!624 = !DISubroutineType(types: !625)
!625 = !{!290, !551, !578, !47}
!626 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !627, file: !465, line: 229)
!627 = !DISubprogram(name: "strtoull", scope: !100, file: !100, line: 206, type: !628, flags: DIFlagPrototyped, spFlags: 0)
!628 = !DISubroutineType(types: !629)
!629 = !{!630, !551, !578, !47}
!630 = !DIBasicType(name: "unsigned long long", size: 64, encoding: DW_ATE_unsigned)
!631 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !632, file: !465, line: 231)
!632 = !DISubprogram(name: "strtof", scope: !100, file: !100, line: 124, type: !633, flags: DIFlagPrototyped, spFlags: 0)
!633 = !DISubroutineType(types: !634)
!634 = !{!168, !551, !578}
!635 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !636, file: !465, line: 232)
!636 = !DISubprogram(name: "strtold", scope: !100, file: !100, line: 127, type: !637, flags: DIFlagPrototyped, spFlags: 0)
!637 = !DISubroutineType(types: !638)
!638 = !{!179, !551, !578}
!639 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !603, file: !465, line: 240)
!640 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !609, file: !465, line: 242)
!641 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !611, file: !465, line: 244)
!642 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !643, file: !465, line: 245)
!643 = !DISubprogram(name: "div", linkageName: "_ZN9__gnu_cxx3divExx", scope: !5, file: !465, line: 213, type: !616, flags: DIFlagPrototyped, spFlags: 0)
!644 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !615, file: !465, line: 246)
!645 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !619, file: !465, line: 248)
!646 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !632, file: !465, line: 249)
!647 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !623, file: !465, line: 250)
!648 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !627, file: !465, line: 251)
!649 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !636, file: !465, line: 252)
!650 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !473, file: !651, line: 38)
!651 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/stdlib.h", directory: "", checksumkind: CSK_MD5, checksum: "0f5b773a303c24013fb112082e6d18a5")
!652 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !477, file: !651, line: 39)
!653 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !516, file: !651, line: 40)
!654 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !482, file: !651, line: 43)
!655 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !561, file: !651, line: 46)
!656 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !463, file: !651, line: 51)
!657 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !467, file: !651, line: 52)
!658 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !444, file: !651, line: 54)
!659 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !484, file: !651, line: 55)
!660 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !486, file: !651, line: 56)
!661 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !490, file: !651, line: 57)
!662 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !494, file: !651, line: 58)
!663 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !508, file: !651, line: 59)
!664 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !643, file: !651, line: 60)
!665 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !520, file: !651, line: 61)
!666 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !524, file: !651, line: 62)
!667 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !529, file: !651, line: 63)
!668 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !533, file: !651, line: 64)
!669 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !537, file: !651, line: 65)
!670 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !541, file: !651, line: 67)
!671 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !545, file: !651, line: 68)
!672 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !553, file: !651, line: 69)
!673 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !557, file: !651, line: 71)
!674 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !563, file: !651, line: 72)
!675 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !567, file: !651, line: 73)
!676 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !571, file: !651, line: 74)
!677 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !575, file: !651, line: 75)
!678 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !581, file: !651, line: 76)
!679 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !585, file: !651, line: 77)
!680 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !589, file: !651, line: 78)
!681 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !591, file: !651, line: 80)
!682 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !0, entity: !599, file: !651, line: 81)
!683 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !684, file: !697, line: 64)
!684 = !DIDerivedType(tag: DW_TAG_typedef, name: "mbstate_t", file: !685, line: 6, baseType: !686)
!685 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/mbstate_t.h", directory: "", checksumkind: CSK_MD5, checksum: "ba8742313715e20e434cf6ccb2db98e3")
!686 = !DIDerivedType(tag: DW_TAG_typedef, name: "__mbstate_t", file: !687, line: 21, baseType: !688)
!687 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/__mbstate_t.h", directory: "", checksumkind: CSK_MD5, checksum: "82911a3e689448e3691ded3e0b471a55")
!688 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !687, line: 13, size: 64, flags: DIFlagTypePassByValue, elements: !689, identifier: "_ZTS11__mbstate_t")
!689 = !{!690, !691}
!690 = !DIDerivedType(tag: DW_TAG_member, name: "__count", scope: !688, file: !687, line: 15, baseType: !47, size: 32)
!691 = !DIDerivedType(tag: DW_TAG_member, name: "__value", scope: !688, file: !687, line: 20, baseType: !692, size: 32, offset: 32)
!692 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !688, file: !687, line: 16, size: 32, flags: DIFlagTypePassByValue, elements: !693, identifier: "_ZTSN11__mbstate_tUt_E")
!693 = !{!694, !695}
!694 = !DIDerivedType(tag: DW_TAG_member, name: "__wch", scope: !692, file: !687, line: 18, baseType: !6, size: 32)
!695 = !DIDerivedType(tag: DW_TAG_member, name: "__wchb", scope: !692, file: !687, line: 19, baseType: !696, size: 32)
!696 = !DICompositeType(tag: DW_TAG_array_type, baseType: !348, size: 32, elements: !88)
!697 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cwchar", directory: "")
!698 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !699, file: !697, line: 141)
!699 = !DIDerivedType(tag: DW_TAG_typedef, name: "wint_t", file: !700, line: 20, baseType: !6)
!700 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/wint_t.h", directory: "", checksumkind: CSK_MD5, checksum: "aa31b53ef28dc23152ceb41e2763ded3")
!701 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !702, file: !697, line: 143)
!702 = !DISubprogram(name: "btowc", scope: !703, file: !703, line: 285, type: !704, flags: DIFlagPrototyped, spFlags: 0)
!703 = !DIFile(filename: "/usr/include/wchar.h", directory: "", checksumkind: CSK_MD5, checksum: "484b7adbbc849bb51cdbcb2d985b07a0")
!704 = !DISubroutineType(types: !705)
!705 = !{!699, !47}
!706 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !707, file: !697, line: 144)
!707 = !DISubprogram(name: "fgetwc", scope: !703, file: !703, line: 744, type: !708, flags: DIFlagPrototyped, spFlags: 0)
!708 = !DISubroutineType(types: !709)
!709 = !{!699, !710}
!710 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !711, size: 64)
!711 = !DIDerivedType(tag: DW_TAG_typedef, name: "__FILE", file: !712, line: 5, baseType: !713)
!712 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/__FILE.h", directory: "", checksumkind: CSK_MD5, checksum: "72a8fe90981f484acae7c6f3dfc5c2b7")
!713 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_FILE", file: !714, line: 49, size: 1728, flags: DIFlagFwdDecl, identifier: "_ZTS8_IO_FILE")
!714 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/struct_FILE.h", directory: "", checksumkind: CSK_MD5, checksum: "1bad07471b7974df4ecc1d1c2ca207e6")
!715 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !716, file: !697, line: 145)
!716 = !DISubprogram(name: "fgetws", scope: !703, file: !703, line: 773, type: !717, flags: DIFlagPrototyped, spFlags: 0)
!717 = !DISubroutineType(types: !718)
!718 = !{!549, !548, !47, !719}
!719 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !710)
!720 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !721, file: !697, line: 146)
!721 = !DISubprogram(name: "fputwc", scope: !703, file: !703, line: 758, type: !722, flags: DIFlagPrototyped, spFlags: 0)
!722 = !DISubroutineType(types: !723)
!723 = !{!699, !550, !710}
!724 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !725, file: !697, line: 147)
!725 = !DISubprogram(name: "fputws", scope: !703, file: !703, line: 780, type: !726, flags: DIFlagPrototyped, spFlags: 0)
!726 = !DISubroutineType(types: !727)
!727 = !{!47, !595, !719}
!728 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !729, file: !697, line: 148)
!729 = !DISubprogram(name: "fwide", scope: !703, file: !703, line: 588, type: !730, flags: DIFlagPrototyped, spFlags: 0)
!730 = !DISubroutineType(types: !731)
!731 = !{!47, !710, !47}
!732 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !733, file: !697, line: 149)
!733 = !DISubprogram(name: "fwprintf", scope: !703, file: !703, line: 595, type: !734, flags: DIFlagPrototyped, spFlags: 0)
!734 = !DISubroutineType(types: !735)
!735 = !{!47, !719, !595, null}
!736 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !737, file: !697, line: 150)
!737 = !DISubprogram(name: "fwscanf", linkageName: "__isoc99_fwscanf", scope: !703, file: !703, line: 657, type: !734, flags: DIFlagPrototyped, spFlags: 0)
!738 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !739, file: !697, line: 151)
!739 = !DISubprogram(name: "getwc", scope: !703, file: !703, line: 745, type: !708, flags: DIFlagPrototyped, spFlags: 0)
!740 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !741, file: !697, line: 152)
!741 = !DISubprogram(name: "getwchar", scope: !703, file: !703, line: 751, type: !742, flags: DIFlagPrototyped, spFlags: 0)
!742 = !DISubroutineType(types: !743)
!743 = !{!699}
!744 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !745, file: !697, line: 153)
!745 = !DISubprogram(name: "mbrlen", scope: !703, file: !703, line: 308, type: !746, flags: DIFlagPrototyped, spFlags: 0)
!746 = !DISubroutineType(types: !747)
!747 = !{!500, !551, !500, !748}
!748 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !749)
!749 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !684, size: 64)
!750 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !751, file: !697, line: 154)
!751 = !DISubprogram(name: "mbrtowc", scope: !703, file: !703, line: 297, type: !752, flags: DIFlagPrototyped, spFlags: 0)
!752 = !DISubroutineType(types: !753)
!753 = !{!500, !548, !551, !500, !748}
!754 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !755, file: !697, line: 155)
!755 = !DISubprogram(name: "mbsinit", scope: !703, file: !703, line: 293, type: !756, flags: DIFlagPrototyped, spFlags: 0)
!756 = !DISubroutineType(types: !757)
!757 = !{!47, !758}
!758 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !759, size: 64)
!759 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !684)
!760 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !761, file: !697, line: 156)
!761 = !DISubprogram(name: "mbsrtowcs", scope: !703, file: !703, line: 338, type: !762, flags: DIFlagPrototyped, spFlags: 0)
!762 = !DISubroutineType(types: !763)
!763 = !{!500, !548, !764, !500, !748}
!764 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !765)
!765 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !346, size: 64)
!766 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !767, file: !697, line: 157)
!767 = !DISubprogram(name: "putwc", scope: !703, file: !703, line: 759, type: !722, flags: DIFlagPrototyped, spFlags: 0)
!768 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !769, file: !697, line: 158)
!769 = !DISubprogram(name: "putwchar", scope: !703, file: !703, line: 765, type: !770, flags: DIFlagPrototyped, spFlags: 0)
!770 = !DISubroutineType(types: !771)
!771 = !{!699, !550}
!772 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !773, file: !697, line: 160)
!773 = !DISubprogram(name: "swprintf", scope: !703, file: !703, line: 605, type: !774, flags: DIFlagPrototyped, spFlags: 0)
!774 = !DISubroutineType(types: !775)
!775 = !{!47, !548, !500, !595, null}
!776 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !777, file: !697, line: 162)
!777 = !DISubprogram(name: "swscanf", linkageName: "__isoc99_swscanf", scope: !703, file: !703, line: 664, type: !778, flags: DIFlagPrototyped, spFlags: 0)
!778 = !DISubroutineType(types: !779)
!779 = !{!47, !595, !595, null}
!780 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !781, file: !697, line: 163)
!781 = !DISubprogram(name: "ungetwc", scope: !703, file: !703, line: 788, type: !782, flags: DIFlagPrototyped, spFlags: 0)
!782 = !DISubroutineType(types: !783)
!783 = !{!699, !699, !710}
!784 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !785, file: !697, line: 164)
!785 = !DISubprogram(name: "vfwprintf", scope: !703, file: !703, line: 613, type: !786, flags: DIFlagPrototyped, spFlags: 0)
!786 = !DISubroutineType(types: !787)
!787 = !{!47, !719, !595, !788}
!788 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !789, size: 64)
!789 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__va_list_tag", size: 192, flags: DIFlagTypePassByValue, elements: !790, identifier: "_ZTS13__va_list_tag")
!790 = !{!791, !793, !794, !795}
!791 = !DIDerivedType(tag: DW_TAG_member, name: "gp_offset", scope: !789, file: !792, baseType: !6, size: 32)
!792 = !DIFile(filename: "LibRaw/src/libraw_c_api.cpp", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729")
!793 = !DIDerivedType(tag: DW_TAG_member, name: "fp_offset", scope: !789, file: !792, baseType: !6, size: 32, offset: 32)
!794 = !DIDerivedType(tag: DW_TAG_member, name: "overflow_arg_area", scope: !789, file: !792, baseType: !497, size: 64, offset: 64)
!795 = !DIDerivedType(tag: DW_TAG_member, name: "reg_save_area", scope: !789, file: !792, baseType: !497, size: 64, offset: 128)
!796 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !797, file: !697, line: 166)
!797 = !DISubprogram(name: "vfwscanf", linkageName: "__isoc99_vfwscanf", scope: !703, file: !703, line: 711, type: !786, flags: DIFlagPrototyped, spFlags: 0)
!798 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !799, file: !697, line: 169)
!799 = !DISubprogram(name: "vswprintf", scope: !703, file: !703, line: 626, type: !800, flags: DIFlagPrototyped, spFlags: 0)
!800 = !DISubroutineType(types: !801)
!801 = !{!47, !548, !500, !595, !788}
!802 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !803, file: !697, line: 172)
!803 = !DISubprogram(name: "vswscanf", linkageName: "__isoc99_vswscanf", scope: !703, file: !703, line: 718, type: !804, flags: DIFlagPrototyped, spFlags: 0)
!804 = !DISubroutineType(types: !805)
!805 = !{!47, !595, !595, !788}
!806 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !807, file: !697, line: 174)
!807 = !DISubprogram(name: "vwprintf", scope: !703, file: !703, line: 621, type: !808, flags: DIFlagPrototyped, spFlags: 0)
!808 = !DISubroutineType(types: !809)
!809 = !{!47, !595, !788}
!810 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !811, file: !697, line: 176)
!811 = !DISubprogram(name: "vwscanf", linkageName: "__isoc99_vwscanf", scope: !703, file: !703, line: 715, type: !808, flags: DIFlagPrototyped, spFlags: 0)
!812 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !813, file: !697, line: 178)
!813 = !DISubprogram(name: "wcrtomb", scope: !703, file: !703, line: 302, type: !814, flags: DIFlagPrototyped, spFlags: 0)
!814 = !DISubroutineType(types: !815)
!815 = !{!500, !594, !550, !748}
!816 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !817, file: !697, line: 179)
!817 = !DISubprogram(name: "wcscat", scope: !703, file: !703, line: 97, type: !818, flags: DIFlagPrototyped, spFlags: 0)
!818 = !DISubroutineType(types: !819)
!819 = !{!549, !548, !595}
!820 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !821, file: !697, line: 180)
!821 = !DISubprogram(name: "wcscmp", scope: !703, file: !703, line: 106, type: !822, flags: DIFlagPrototyped, spFlags: 0)
!822 = !DISubroutineType(types: !823)
!823 = !{!47, !596, !596}
!824 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !825, file: !697, line: 181)
!825 = !DISubprogram(name: "wcscoll", scope: !703, file: !703, line: 131, type: !822, flags: DIFlagPrototyped, spFlags: 0)
!826 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !827, file: !697, line: 182)
!827 = !DISubprogram(name: "wcscpy", scope: !703, file: !703, line: 87, type: !818, flags: DIFlagPrototyped, spFlags: 0)
!828 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !829, file: !697, line: 183)
!829 = !DISubprogram(name: "wcscspn", scope: !703, file: !703, line: 188, type: !830, flags: DIFlagPrototyped, spFlags: 0)
!830 = !DISubroutineType(types: !831)
!831 = !{!500, !596, !596}
!832 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !833, file: !697, line: 184)
!833 = !DISubprogram(name: "wcsftime", scope: !703, file: !703, line: 852, type: !834, flags: DIFlagPrototyped, spFlags: 0)
!834 = !DISubroutineType(types: !835)
!835 = !{!500, !548, !500, !595, !836}
!836 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !837)
!837 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !838, size: 64)
!838 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !839)
!839 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "tm", file: !840, line: 7, size: 448, flags: DIFlagTypePassByValue, elements: !841, identifier: "_ZTS2tm")
!840 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/struct_tm.h", directory: "", checksumkind: CSK_MD5, checksum: "9e5545b565ef031c4cd0faf90b69386f")
!841 = !{!842, !843, !844, !845, !846, !847, !848, !849, !850, !851, !852}
!842 = !DIDerivedType(tag: DW_TAG_member, name: "tm_sec", scope: !839, file: !840, line: 9, baseType: !47, size: 32)
!843 = !DIDerivedType(tag: DW_TAG_member, name: "tm_min", scope: !839, file: !840, line: 10, baseType: !47, size: 32, offset: 32)
!844 = !DIDerivedType(tag: DW_TAG_member, name: "tm_hour", scope: !839, file: !840, line: 11, baseType: !47, size: 32, offset: 64)
!845 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mday", scope: !839, file: !840, line: 12, baseType: !47, size: 32, offset: 96)
!846 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mon", scope: !839, file: !840, line: 13, baseType: !47, size: 32, offset: 128)
!847 = !DIDerivedType(tag: DW_TAG_member, name: "tm_year", scope: !839, file: !840, line: 14, baseType: !47, size: 32, offset: 160)
!848 = !DIDerivedType(tag: DW_TAG_member, name: "tm_wday", scope: !839, file: !840, line: 15, baseType: !47, size: 32, offset: 192)
!849 = !DIDerivedType(tag: DW_TAG_member, name: "tm_yday", scope: !839, file: !840, line: 16, baseType: !47, size: 32, offset: 224)
!850 = !DIDerivedType(tag: DW_TAG_member, name: "tm_isdst", scope: !839, file: !840, line: 17, baseType: !47, size: 32, offset: 256)
!851 = !DIDerivedType(tag: DW_TAG_member, name: "tm_gmtoff", scope: !839, file: !840, line: 20, baseType: !327, size: 64, offset: 320)
!852 = !DIDerivedType(tag: DW_TAG_member, name: "tm_zone", scope: !839, file: !840, line: 21, baseType: !346, size: 64, offset: 384)
!853 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !854, file: !697, line: 185)
!854 = !DISubprogram(name: "wcslen", scope: !703, file: !703, line: 223, type: !855, flags: DIFlagPrototyped, spFlags: 0)
!855 = !DISubroutineType(types: !856)
!856 = !{!500, !596}
!857 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !858, file: !697, line: 186)
!858 = !DISubprogram(name: "wcsncat", scope: !703, file: !703, line: 101, type: !859, flags: DIFlagPrototyped, spFlags: 0)
!859 = !DISubroutineType(types: !860)
!860 = !{!549, !548, !595, !500}
!861 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !862, file: !697, line: 187)
!862 = !DISubprogram(name: "wcsncmp", scope: !703, file: !703, line: 109, type: !863, flags: DIFlagPrototyped, spFlags: 0)
!863 = !DISubroutineType(types: !864)
!864 = !{!47, !596, !596, !500}
!865 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !866, file: !697, line: 188)
!866 = !DISubprogram(name: "wcsncpy", scope: !703, file: !703, line: 92, type: !859, flags: DIFlagPrototyped, spFlags: 0)
!867 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !868, file: !697, line: 189)
!868 = !DISubprogram(name: "wcsrtombs", scope: !703, file: !703, line: 344, type: !869, flags: DIFlagPrototyped, spFlags: 0)
!869 = !DISubroutineType(types: !870)
!870 = !{!500, !594, !871, !500, !748}
!871 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !872)
!872 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !596, size: 64)
!873 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !874, file: !697, line: 190)
!874 = !DISubprogram(name: "wcsspn", scope: !703, file: !703, line: 192, type: !830, flags: DIFlagPrototyped, spFlags: 0)
!875 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !876, file: !697, line: 191)
!876 = !DISubprogram(name: "wcstod", scope: !703, file: !703, line: 378, type: !877, flags: DIFlagPrototyped, spFlags: 0)
!877 = !DISubroutineType(types: !878)
!878 = !{!109, !595, !879}
!879 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !880)
!880 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !549, size: 64)
!881 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !882, file: !697, line: 193)
!882 = !DISubprogram(name: "wcstof", scope: !703, file: !703, line: 383, type: !883, flags: DIFlagPrototyped, spFlags: 0)
!883 = !DISubroutineType(types: !884)
!884 = !{!168, !595, !879}
!885 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !886, file: !697, line: 195)
!886 = !DISubprogram(name: "wcstok", scope: !703, file: !703, line: 218, type: !887, flags: DIFlagPrototyped, spFlags: 0)
!887 = !DISubroutineType(types: !888)
!888 = !{!549, !548, !595, !879}
!889 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !890, file: !697, line: 196)
!890 = !DISubprogram(name: "wcstol", scope: !703, file: !703, line: 429, type: !891, flags: DIFlagPrototyped, spFlags: 0)
!891 = !DISubroutineType(types: !892)
!892 = !{!327, !595, !879, !47}
!893 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !894, file: !697, line: 197)
!894 = !DISubprogram(name: "wcstoul", scope: !703, file: !703, line: 434, type: !895, flags: DIFlagPrototyped, spFlags: 0)
!895 = !DISubroutineType(types: !896)
!896 = !{!502, !595, !879, !47}
!897 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !898, file: !697, line: 198)
!898 = !DISubprogram(name: "wcsxfrm", scope: !703, file: !703, line: 135, type: !899, flags: DIFlagPrototyped, spFlags: 0)
!899 = !DISubroutineType(types: !900)
!900 = !{!500, !548, !595, !500}
!901 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !902, file: !697, line: 199)
!902 = !DISubprogram(name: "wctob", scope: !703, file: !703, line: 289, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!903 = !DISubroutineType(types: !904)
!904 = !{!47, !699}
!905 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !906, file: !697, line: 200)
!906 = !DISubprogram(name: "wmemcmp", scope: !703, file: !703, line: 259, type: !863, flags: DIFlagPrototyped, spFlags: 0)
!907 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !908, file: !697, line: 201)
!908 = !DISubprogram(name: "wmemcpy", scope: !703, file: !703, line: 263, type: !859, flags: DIFlagPrototyped, spFlags: 0)
!909 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !910, file: !697, line: 202)
!910 = !DISubprogram(name: "wmemmove", scope: !703, file: !703, line: 268, type: !911, flags: DIFlagPrototyped, spFlags: 0)
!911 = !DISubroutineType(types: !912)
!912 = !{!549, !549, !596, !500}
!913 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !914, file: !697, line: 203)
!914 = !DISubprogram(name: "wmemset", scope: !703, file: !703, line: 272, type: !915, flags: DIFlagPrototyped, spFlags: 0)
!915 = !DISubroutineType(types: !916)
!916 = !{!549, !549, !550, !500}
!917 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !918, file: !697, line: 204)
!918 = !DISubprogram(name: "wprintf", scope: !703, file: !703, line: 602, type: !919, flags: DIFlagPrototyped, spFlags: 0)
!919 = !DISubroutineType(types: !920)
!920 = !{!47, !595, null}
!921 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !922, file: !697, line: 205)
!922 = !DISubprogram(name: "wscanf", linkageName: "__isoc99_wscanf", scope: !703, file: !703, line: 661, type: !919, flags: DIFlagPrototyped, spFlags: 0)
!923 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !924, file: !697, line: 206)
!924 = !DISubprogram(name: "wcschr", scope: !703, file: !703, line: 165, type: !925, flags: DIFlagPrototyped, spFlags: 0)
!925 = !DISubroutineType(types: !926)
!926 = !{!549, !596, !550}
!927 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !928, file: !697, line: 207)
!928 = !DISubprogram(name: "wcspbrk", scope: !703, file: !703, line: 202, type: !929, flags: DIFlagPrototyped, spFlags: 0)
!929 = !DISubroutineType(types: !930)
!930 = !{!549, !596, !596}
!931 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !932, file: !697, line: 208)
!932 = !DISubprogram(name: "wcsrchr", scope: !703, file: !703, line: 175, type: !925, flags: DIFlagPrototyped, spFlags: 0)
!933 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !934, file: !697, line: 209)
!934 = !DISubprogram(name: "wcsstr", scope: !703, file: !703, line: 213, type: !929, flags: DIFlagPrototyped, spFlags: 0)
!935 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !936, file: !697, line: 210)
!936 = !DISubprogram(name: "wmemchr", scope: !703, file: !703, line: 254, type: !937, flags: DIFlagPrototyped, spFlags: 0)
!937 = !DISubroutineType(types: !938)
!938 = !{!549, !596, !550, !500}
!939 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !940, file: !697, line: 251)
!940 = !DISubprogram(name: "wcstold", scope: !703, file: !703, line: 385, type: !941, flags: DIFlagPrototyped, spFlags: 0)
!941 = !DISubroutineType(types: !942)
!942 = !{!179, !595, !879}
!943 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !944, file: !697, line: 260)
!944 = !DISubprogram(name: "wcstoll", scope: !703, file: !703, line: 442, type: !945, flags: DIFlagPrototyped, spFlags: 0)
!945 = !DISubroutineType(types: !946)
!946 = !{!290, !595, !879, !47}
!947 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !948, file: !697, line: 261)
!948 = !DISubprogram(name: "wcstoull", scope: !703, file: !703, line: 449, type: !949, flags: DIFlagPrototyped, spFlags: 0)
!949 = !DISubroutineType(types: !950)
!950 = !{!630, !595, !879, !47}
!951 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !940, file: !697, line: 267)
!952 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !944, file: !697, line: 268)
!953 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !948, file: !697, line: 269)
!954 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !882, file: !697, line: 283)
!955 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !797, file: !697, line: 286)
!956 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !803, file: !697, line: 289)
!957 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !811, file: !697, line: 292)
!958 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !940, file: !697, line: 296)
!959 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !944, file: !697, line: 297)
!960 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !948, file: !697, line: 298)
!961 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !962, entity: !963, file: !964, line: 58)
!962 = !DINamespace(name: "__gnu_debug", scope: null)
!963 = !DINamespace(name: "__debug", scope: !98)
!964 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/debug/debug.h", directory: "", checksumkind: CSK_MD5, checksum: "982c0103e1e5f86b0818efdfc5273c3c")
!965 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !966, file: !971, line: 47)
!966 = !DIDerivedType(tag: DW_TAG_typedef, name: "int8_t", file: !967, line: 24, baseType: !968)
!967 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/stdint-intn.h", directory: "", checksumkind: CSK_MD5, checksum: "55bcbdc3159515ebd91d351a70d505f4")
!968 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int8_t", file: !969, line: 37, baseType: !970)
!969 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types.h", directory: "", checksumkind: CSK_MD5, checksum: "d108b5f93a74c50510d7d9bc0ab36df9")
!970 = !DIBasicType(name: "signed char", size: 8, encoding: DW_ATE_signed_char)
!971 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cstdint", directory: "")
!972 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !973, file: !971, line: 48)
!973 = !DIDerivedType(tag: DW_TAG_typedef, name: "int16_t", file: !967, line: 25, baseType: !974)
!974 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int16_t", file: !969, line: 39, baseType: !975)
!975 = !DIBasicType(name: "short", size: 16, encoding: DW_ATE_signed)
!976 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !977, file: !971, line: 49)
!977 = !DIDerivedType(tag: DW_TAG_typedef, name: "int32_t", file: !967, line: 26, baseType: !978)
!978 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int32_t", file: !969, line: 41, baseType: !47)
!979 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !980, file: !971, line: 50)
!980 = !DIDerivedType(tag: DW_TAG_typedef, name: "int64_t", file: !967, line: 27, baseType: !981)
!981 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int64_t", file: !969, line: 44, baseType: !327)
!982 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !983, file: !971, line: 52)
!983 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_fast8_t", file: !984, line: 58, baseType: !970)
!984 = !DIFile(filename: "/usr/include/stdint.h", directory: "", checksumkind: CSK_MD5, checksum: "a48e64edacc5b19f56c99745232c963c")
!985 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !986, file: !971, line: 53)
!986 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_fast16_t", file: !984, line: 60, baseType: !327)
!987 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !988, file: !971, line: 54)
!988 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_fast32_t", file: !984, line: 61, baseType: !327)
!989 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !990, file: !971, line: 55)
!990 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_fast64_t", file: !984, line: 62, baseType: !327)
!991 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !992, file: !971, line: 57)
!992 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_least8_t", file: !984, line: 43, baseType: !993)
!993 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int_least8_t", file: !969, line: 52, baseType: !968)
!994 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !995, file: !971, line: 58)
!995 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_least16_t", file: !984, line: 44, baseType: !996)
!996 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int_least16_t", file: !969, line: 54, baseType: !974)
!997 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !998, file: !971, line: 59)
!998 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_least32_t", file: !984, line: 45, baseType: !999)
!999 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int_least32_t", file: !969, line: 56, baseType: !978)
!1000 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1001, file: !971, line: 60)
!1001 = !DIDerivedType(tag: DW_TAG_typedef, name: "int_least64_t", file: !984, line: 46, baseType: !1002)
!1002 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int_least64_t", file: !969, line: 58, baseType: !981)
!1003 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1004, file: !971, line: 62)
!1004 = !DIDerivedType(tag: DW_TAG_typedef, name: "intmax_t", file: !984, line: 101, baseType: !1005)
!1005 = !DIDerivedType(tag: DW_TAG_typedef, name: "__intmax_t", file: !969, line: 72, baseType: !327)
!1006 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1007, file: !971, line: 63)
!1007 = !DIDerivedType(tag: DW_TAG_typedef, name: "intptr_t", file: !984, line: 87, baseType: !327)
!1008 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1009, file: !971, line: 65)
!1009 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !1010, line: 24, baseType: !1011)
!1010 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h", directory: "", checksumkind: CSK_MD5, checksum: "2bf2ae53c58c01b1a1b9383b5195125c")
!1011 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint8_t", file: !969, line: 38, baseType: !91)
!1012 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1013, file: !971, line: 66)
!1013 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint16_t", file: !1010, line: 25, baseType: !1014)
!1014 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint16_t", file: !969, line: 40, baseType: !85)
!1015 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1016, file: !971, line: 67)
!1016 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !1010, line: 26, baseType: !1017)
!1017 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint32_t", file: !969, line: 42, baseType: !6)
!1018 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1019, file: !971, line: 68)
!1019 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint64_t", file: !1010, line: 27, baseType: !1020)
!1020 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint64_t", file: !969, line: 45, baseType: !502)
!1021 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1022, file: !971, line: 70)
!1022 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_fast8_t", file: !984, line: 71, baseType: !91)
!1023 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1024, file: !971, line: 71)
!1024 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_fast16_t", file: !984, line: 73, baseType: !502)
!1025 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1026, file: !971, line: 72)
!1026 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_fast32_t", file: !984, line: 74, baseType: !502)
!1027 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1028, file: !971, line: 73)
!1028 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_fast64_t", file: !984, line: 75, baseType: !502)
!1029 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1030, file: !971, line: 75)
!1030 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_least8_t", file: !984, line: 49, baseType: !1031)
!1031 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint_least8_t", file: !969, line: 53, baseType: !1011)
!1032 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1033, file: !971, line: 76)
!1033 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_least16_t", file: !984, line: 50, baseType: !1034)
!1034 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint_least16_t", file: !969, line: 55, baseType: !1014)
!1035 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1036, file: !971, line: 77)
!1036 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_least32_t", file: !984, line: 51, baseType: !1037)
!1037 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint_least32_t", file: !969, line: 57, baseType: !1017)
!1038 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1039, file: !971, line: 78)
!1039 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint_least64_t", file: !984, line: 52, baseType: !1040)
!1040 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uint_least64_t", file: !969, line: 59, baseType: !1020)
!1041 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1042, file: !971, line: 80)
!1042 = !DIDerivedType(tag: DW_TAG_typedef, name: "uintmax_t", file: !984, line: 102, baseType: !1043)
!1043 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uintmax_t", file: !969, line: 73, baseType: !502)
!1044 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1045, file: !971, line: 81)
!1045 = !DIDerivedType(tag: DW_TAG_typedef, name: "uintptr_t", file: !984, line: 90, baseType: !502)
!1046 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1047, file: !1049, line: 53)
!1047 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "lconv", file: !1048, line: 51, size: 768, flags: DIFlagFwdDecl, identifier: "_ZTS5lconv")
!1048 = !DIFile(filename: "/usr/include/locale.h", directory: "", checksumkind: CSK_MD5, checksum: "a1d177e0f311dc60a74cb347049d75bc")
!1049 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/clocale", directory: "")
!1050 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1051, file: !1049, line: 54)
!1051 = !DISubprogram(name: "setlocale", scope: !1048, file: !1048, line: 122, type: !1052, flags: DIFlagPrototyped, spFlags: 0)
!1052 = !DISubroutineType(types: !1053)
!1053 = !{!527, !47, !346}
!1054 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1055, file: !1049, line: 55)
!1055 = !DISubprogram(name: "localeconv", scope: !1048, file: !1048, line: 125, type: !1056, flags: DIFlagPrototyped, spFlags: 0)
!1056 = !DISubroutineType(types: !1057)
!1057 = !{!1058}
!1058 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1047, size: 64)
!1059 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1060, file: !1062, line: 64)
!1060 = !DISubprogram(name: "isalnum", scope: !1061, file: !1061, line: 108, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1061 = !DIFile(filename: "/usr/include/ctype.h", directory: "", checksumkind: CSK_MD5, checksum: "3ab3dd7fdf2578005732722ee2393e59")
!1062 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cctype", directory: "")
!1063 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1064, file: !1062, line: 65)
!1064 = !DISubprogram(name: "isalpha", scope: !1061, file: !1061, line: 109, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1065 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1066, file: !1062, line: 66)
!1066 = !DISubprogram(name: "iscntrl", scope: !1061, file: !1061, line: 110, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1067 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1068, file: !1062, line: 67)
!1068 = !DISubprogram(name: "isdigit", scope: !1061, file: !1061, line: 111, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1069 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1070, file: !1062, line: 68)
!1070 = !DISubprogram(name: "isgraph", scope: !1061, file: !1061, line: 113, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1071 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1072, file: !1062, line: 69)
!1072 = !DISubprogram(name: "islower", scope: !1061, file: !1061, line: 112, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1073 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1074, file: !1062, line: 70)
!1074 = !DISubprogram(name: "isprint", scope: !1061, file: !1061, line: 114, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1075 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1076, file: !1062, line: 71)
!1076 = !DISubprogram(name: "ispunct", scope: !1061, file: !1061, line: 115, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1077 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1078, file: !1062, line: 72)
!1078 = !DISubprogram(name: "isspace", scope: !1061, file: !1061, line: 116, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1079 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1080, file: !1062, line: 73)
!1080 = !DISubprogram(name: "isupper", scope: !1061, file: !1061, line: 117, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1081 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1082, file: !1062, line: 74)
!1082 = !DISubprogram(name: "isxdigit", scope: !1061, file: !1061, line: 118, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1083 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1084, file: !1062, line: 75)
!1084 = !DISubprogram(name: "tolower", scope: !1061, file: !1061, line: 122, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1085 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1086, file: !1062, line: 76)
!1086 = !DISubprogram(name: "toupper", scope: !1061, file: !1061, line: 125, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1087 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1088, file: !1062, line: 87)
!1088 = !DISubprogram(name: "isblank", scope: !1061, file: !1061, line: 130, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1089 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1090, file: !1092, line: 98)
!1090 = !DIDerivedType(tag: DW_TAG_typedef, name: "FILE", file: !1091, line: 7, baseType: !713)
!1091 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/FILE.h", directory: "", checksumkind: CSK_MD5, checksum: "571f9fb6223c42439075fdde11a0de5d")
!1092 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cstdio", directory: "")
!1093 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1094, file: !1092, line: 99)
!1094 = !DIDerivedType(tag: DW_TAG_typedef, name: "fpos_t", file: !1095, line: 84, baseType: !1096)
!1095 = !DIFile(filename: "/usr/include/stdio.h", directory: "", checksumkind: CSK_MD5, checksum: "f31eefcc3f15835fc5a4023a625cf609")
!1096 = !DIDerivedType(tag: DW_TAG_typedef, name: "__fpos_t", file: !1097, line: 14, baseType: !1098)
!1097 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/types/__fpos_t.h", directory: "", checksumkind: CSK_MD5, checksum: "32de8bdaf3551a6c0a9394f9af4389ce")
!1098 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_G_fpos_t", file: !1097, line: 10, size: 128, flags: DIFlagFwdDecl, identifier: "_ZTS9_G_fpos_t")
!1099 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1100, file: !1092, line: 101)
!1100 = !DISubprogram(name: "clearerr", scope: !1095, file: !1095, line: 786, type: !1101, flags: DIFlagPrototyped, spFlags: 0)
!1101 = !DISubroutineType(types: !1102)
!1102 = !{null, !1103}
!1103 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1090, size: 64)
!1104 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1105, file: !1092, line: 102)
!1105 = !DISubprogram(name: "fclose", scope: !1095, file: !1095, line: 178, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1106 = !DISubroutineType(types: !1107)
!1107 = !{!47, !1103}
!1108 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1109, file: !1092, line: 103)
!1109 = !DISubprogram(name: "feof", scope: !1095, file: !1095, line: 788, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1110 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1111, file: !1092, line: 104)
!1111 = !DISubprogram(name: "ferror", scope: !1095, file: !1095, line: 790, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1112 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1113, file: !1092, line: 105)
!1113 = !DISubprogram(name: "fflush", scope: !1095, file: !1095, line: 230, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1114 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1115, file: !1092, line: 106)
!1115 = !DISubprogram(name: "fgetc", scope: !1095, file: !1095, line: 513, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1116 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1117, file: !1092, line: 107)
!1117 = !DISubprogram(name: "fgetpos", scope: !1095, file: !1095, line: 760, type: !1118, flags: DIFlagPrototyped, spFlags: 0)
!1118 = !DISubroutineType(types: !1119)
!1119 = !{!47, !1120, !1121}
!1120 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !1103)
!1121 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !1122)
!1122 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1094, size: 64)
!1123 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1124, file: !1092, line: 108)
!1124 = !DISubprogram(name: "fgets", scope: !1095, file: !1095, line: 592, type: !1125, flags: DIFlagPrototyped, spFlags: 0)
!1125 = !DISubroutineType(types: !1126)
!1126 = !{!527, !594, !47, !1120}
!1127 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1128, file: !1092, line: 109)
!1128 = !DISubprogram(name: "fopen", scope: !1095, file: !1095, line: 258, type: !1129, flags: DIFlagPrototyped, spFlags: 0)
!1129 = !DISubroutineType(types: !1130)
!1130 = !{!1103, !551, !551}
!1131 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1132, file: !1092, line: 110)
!1132 = !DISubprogram(name: "fprintf", scope: !1095, file: !1095, line: 350, type: !1133, flags: DIFlagPrototyped, spFlags: 0)
!1133 = !DISubroutineType(types: !1134)
!1134 = !{!47, !1120, !551, null}
!1135 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1136, file: !1092, line: 111)
!1136 = !DISubprogram(name: "fputc", scope: !1095, file: !1095, line: 549, type: !1137, flags: DIFlagPrototyped, spFlags: 0)
!1137 = !DISubroutineType(types: !1138)
!1138 = !{!47, !47, !1103}
!1139 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1140, file: !1092, line: 112)
!1140 = !DISubprogram(name: "fputs", scope: !1095, file: !1095, line: 655, type: !1141, flags: DIFlagPrototyped, spFlags: 0)
!1141 = !DISubroutineType(types: !1142)
!1142 = !{!47, !551, !1120}
!1143 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1144, file: !1092, line: 113)
!1144 = !DISubprogram(name: "fread", scope: !1095, file: !1095, line: 675, type: !1145, flags: DIFlagPrototyped, spFlags: 0)
!1145 = !DISubroutineType(types: !1146)
!1146 = !{!500, !1147, !500, !500, !1120}
!1147 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !497)
!1148 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1149, file: !1092, line: 114)
!1149 = !DISubprogram(name: "freopen", scope: !1095, file: !1095, line: 265, type: !1150, flags: DIFlagPrototyped, spFlags: 0)
!1150 = !DISubroutineType(types: !1151)
!1151 = !{!1103, !551, !551, !1120}
!1152 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1153, file: !1092, line: 115)
!1153 = !DISubprogram(name: "fscanf", linkageName: "__isoc99_fscanf", scope: !1095, file: !1095, line: 434, type: !1133, flags: DIFlagPrototyped, spFlags: 0)
!1154 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1155, file: !1092, line: 116)
!1155 = !DISubprogram(name: "fseek", scope: !1095, file: !1095, line: 713, type: !1156, flags: DIFlagPrototyped, spFlags: 0)
!1156 = !DISubroutineType(types: !1157)
!1157 = !{!47, !1103, !327, !47}
!1158 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1159, file: !1092, line: 117)
!1159 = !DISubprogram(name: "fsetpos", scope: !1095, file: !1095, line: 765, type: !1160, flags: DIFlagPrototyped, spFlags: 0)
!1160 = !DISubroutineType(types: !1161)
!1161 = !{!47, !1103, !1162}
!1162 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1163, size: 64)
!1163 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !1094)
!1164 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1165, file: !1092, line: 118)
!1165 = !DISubprogram(name: "ftell", scope: !1095, file: !1095, line: 718, type: !1166, flags: DIFlagPrototyped, spFlags: 0)
!1166 = !DISubroutineType(types: !1167)
!1167 = !{!327, !1103}
!1168 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1169, file: !1092, line: 119)
!1169 = !DISubprogram(name: "fwrite", scope: !1095, file: !1095, line: 681, type: !1170, flags: DIFlagPrototyped, spFlags: 0)
!1170 = !DISubroutineType(types: !1171)
!1171 = !{!500, !1172, !500, !500, !1120}
!1172 = !DIDerivedType(tag: DW_TAG_restrict_type, baseType: !498)
!1173 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1174, file: !1092, line: 120)
!1174 = !DISubprogram(name: "getc", scope: !1095, file: !1095, line: 514, type: !1106, flags: DIFlagPrototyped, spFlags: 0)
!1175 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1176, file: !1092, line: 121)
!1176 = !DISubprogram(name: "getchar", scope: !1095, file: !1095, line: 520, type: !564, flags: DIFlagPrototyped, spFlags: 0)
!1177 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1178, file: !1092, line: 126)
!1178 = !DISubprogram(name: "perror", scope: !1095, file: !1095, line: 804, type: !1179, flags: DIFlagPrototyped, spFlags: 0)
!1179 = !DISubroutineType(types: !1180)
!1180 = !{null, !346}
!1181 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1182, file: !1092, line: 127)
!1182 = !DISubprogram(name: "printf", scope: !1095, file: !1095, line: 356, type: !1183, flags: DIFlagPrototyped, spFlags: 0)
!1183 = !DISubroutineType(types: !1184)
!1184 = !{!47, !551, null}
!1185 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1186, file: !1092, line: 128)
!1186 = !DISubprogram(name: "putc", scope: !1095, file: !1095, line: 550, type: !1137, flags: DIFlagPrototyped, spFlags: 0)
!1187 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1188, file: !1092, line: 129)
!1188 = !DISubprogram(name: "putchar", scope: !1095, file: !1095, line: 556, type: !101, flags: DIFlagPrototyped, spFlags: 0)
!1189 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1190, file: !1092, line: 130)
!1190 = !DISubprogram(name: "puts", scope: !1095, file: !1095, line: 661, type: !487, flags: DIFlagPrototyped, spFlags: 0)
!1191 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1192, file: !1092, line: 131)
!1192 = !DISubprogram(name: "remove", scope: !1095, file: !1095, line: 152, type: !487, flags: DIFlagPrototyped, spFlags: 0)
!1193 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1194, file: !1092, line: 132)
!1194 = !DISubprogram(name: "rename", scope: !1095, file: !1095, line: 154, type: !1195, flags: DIFlagPrototyped, spFlags: 0)
!1195 = !DISubroutineType(types: !1196)
!1196 = !{!47, !346, !346}
!1197 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1198, file: !1092, line: 133)
!1198 = !DISubprogram(name: "rewind", scope: !1095, file: !1095, line: 723, type: !1101, flags: DIFlagPrototyped, spFlags: 0)
!1199 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1200, file: !1092, line: 134)
!1200 = !DISubprogram(name: "scanf", linkageName: "__isoc99_scanf", scope: !1095, file: !1095, line: 437, type: !1183, flags: DIFlagPrototyped, spFlags: 0)
!1201 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1202, file: !1092, line: 135)
!1202 = !DISubprogram(name: "setbuf", scope: !1095, file: !1095, line: 328, type: !1203, flags: DIFlagPrototyped, spFlags: 0)
!1203 = !DISubroutineType(types: !1204)
!1204 = !{null, !1120, !594}
!1205 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1206, file: !1092, line: 136)
!1206 = !DISubprogram(name: "setvbuf", scope: !1095, file: !1095, line: 332, type: !1207, flags: DIFlagPrototyped, spFlags: 0)
!1207 = !DISubroutineType(types: !1208)
!1208 = !{!47, !1120, !594, !47, !500}
!1209 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1210, file: !1092, line: 137)
!1210 = !DISubprogram(name: "sprintf", scope: !1095, file: !1095, line: 358, type: !1211, flags: DIFlagPrototyped, spFlags: 0)
!1211 = !DISubroutineType(types: !1212)
!1212 = !{!47, !594, !551, null}
!1213 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1214, file: !1092, line: 138)
!1214 = !DISubprogram(name: "sscanf", linkageName: "__isoc99_sscanf", scope: !1095, file: !1095, line: 439, type: !1215, flags: DIFlagPrototyped, spFlags: 0)
!1215 = !DISubroutineType(types: !1216)
!1216 = !{!47, !551, !551, null}
!1217 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1218, file: !1092, line: 139)
!1218 = !DISubprogram(name: "tmpfile", scope: !1095, file: !1095, line: 188, type: !1219, flags: DIFlagPrototyped, spFlags: 0)
!1219 = !DISubroutineType(types: !1220)
!1220 = !{!1103}
!1221 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1222, file: !1092, line: 141)
!1222 = !DISubprogram(name: "tmpnam", scope: !1095, file: !1095, line: 205, type: !1223, flags: DIFlagPrototyped, spFlags: 0)
!1223 = !DISubroutineType(types: !1224)
!1224 = !{!527, !527}
!1225 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1226, file: !1092, line: 143)
!1226 = !DISubprogram(name: "ungetc", scope: !1095, file: !1095, line: 668, type: !1137, flags: DIFlagPrototyped, spFlags: 0)
!1227 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1228, file: !1092, line: 144)
!1228 = !DISubprogram(name: "vfprintf", scope: !1095, file: !1095, line: 365, type: !1229, flags: DIFlagPrototyped, spFlags: 0)
!1229 = !DISubroutineType(types: !1230)
!1230 = !{!47, !1120, !551, !788}
!1231 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1232, file: !1092, line: 145)
!1232 = !DISubprogram(name: "vprintf", scope: !1095, file: !1095, line: 371, type: !1233, flags: DIFlagPrototyped, spFlags: 0)
!1233 = !DISubroutineType(types: !1234)
!1234 = !{!47, !551, !788}
!1235 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1236, file: !1092, line: 146)
!1236 = !DISubprogram(name: "vsprintf", scope: !1095, file: !1095, line: 373, type: !1237, flags: DIFlagPrototyped, spFlags: 0)
!1237 = !DISubroutineType(types: !1238)
!1238 = !{!47, !594, !551, !788}
!1239 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !1240, file: !1092, line: 175)
!1240 = !DISubprogram(name: "snprintf", scope: !1095, file: !1095, line: 378, type: !1241, flags: DIFlagPrototyped, spFlags: 0)
!1241 = !DISubroutineType(types: !1242)
!1242 = !{!47, !594, !500, !551, null}
!1243 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !1244, file: !1092, line: 176)
!1244 = !DISubprogram(name: "vfscanf", linkageName: "__isoc99_vfscanf", scope: !1095, file: !1095, line: 479, type: !1229, flags: DIFlagPrototyped, spFlags: 0)
!1245 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !1246, file: !1092, line: 177)
!1246 = !DISubprogram(name: "vscanf", linkageName: "__isoc99_vscanf", scope: !1095, file: !1095, line: 484, type: !1233, flags: DIFlagPrototyped, spFlags: 0)
!1247 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !1248, file: !1092, line: 178)
!1248 = !DISubprogram(name: "vsnprintf", scope: !1095, file: !1095, line: 382, type: !1249, flags: DIFlagPrototyped, spFlags: 0)
!1249 = !DISubroutineType(types: !1250)
!1250 = !{!47, !594, !500, !551, !788}
!1251 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !5, entity: !1252, file: !1092, line: 179)
!1252 = !DISubprogram(name: "vsscanf", linkageName: "__isoc99_vsscanf", scope: !1095, file: !1095, line: 487, type: !1253, flags: DIFlagPrototyped, spFlags: 0)
!1253 = !DISubroutineType(types: !1254)
!1254 = !{!47, !551, !551, !788}
!1255 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1240, file: !1092, line: 185)
!1256 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1244, file: !1092, line: 186)
!1257 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1246, file: !1092, line: 187)
!1258 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1248, file: !1092, line: 188)
!1259 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1252, file: !1092, line: 189)
!1260 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1261, file: !1265, line: 82)
!1261 = !DIDerivedType(tag: DW_TAG_typedef, name: "wctrans_t", file: !1262, line: 48, baseType: !1263)
!1262 = !DIFile(filename: "/usr/include/wctype.h", directory: "", checksumkind: CSK_MD5, checksum: "9bcd8e8b8cd2078c8a6c42e262af7d7b")
!1263 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1264, size: 64)
!1264 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !978)
!1265 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/cwctype", directory: "")
!1266 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1267, file: !1265, line: 83)
!1267 = !DIDerivedType(tag: DW_TAG_typedef, name: "wctype_t", file: !1268, line: 38, baseType: !502)
!1268 = !DIFile(filename: "/usr/include/x86_64-linux-gnu/bits/wctype-wchar.h", directory: "", checksumkind: CSK_MD5, checksum: "48fed714a84c77fca0455b433489fc47")
!1269 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !699, file: !1265, line: 84)
!1270 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1271, file: !1265, line: 86)
!1271 = !DISubprogram(name: "iswalnum", scope: !1268, file: !1268, line: 95, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1272 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1273, file: !1265, line: 87)
!1273 = !DISubprogram(name: "iswalpha", scope: !1268, file: !1268, line: 101, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1274 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1275, file: !1265, line: 89)
!1275 = !DISubprogram(name: "iswblank", scope: !1268, file: !1268, line: 146, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1276 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1277, file: !1265, line: 91)
!1277 = !DISubprogram(name: "iswcntrl", scope: !1268, file: !1268, line: 104, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1278 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1279, file: !1265, line: 92)
!1279 = !DISubprogram(name: "iswctype", scope: !1268, file: !1268, line: 159, type: !1280, flags: DIFlagPrototyped, spFlags: 0)
!1280 = !DISubroutineType(types: !1281)
!1281 = !{!47, !699, !1267}
!1282 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1283, file: !1265, line: 93)
!1283 = !DISubprogram(name: "iswdigit", scope: !1268, file: !1268, line: 108, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1284 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1285, file: !1265, line: 94)
!1285 = !DISubprogram(name: "iswgraph", scope: !1268, file: !1268, line: 112, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1286 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1287, file: !1265, line: 95)
!1287 = !DISubprogram(name: "iswlower", scope: !1268, file: !1268, line: 117, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1288 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1289, file: !1265, line: 96)
!1289 = !DISubprogram(name: "iswprint", scope: !1268, file: !1268, line: 120, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1290 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1291, file: !1265, line: 97)
!1291 = !DISubprogram(name: "iswpunct", scope: !1268, file: !1268, line: 125, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1292 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1293, file: !1265, line: 98)
!1293 = !DISubprogram(name: "iswspace", scope: !1268, file: !1268, line: 130, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1294 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1295, file: !1265, line: 99)
!1295 = !DISubprogram(name: "iswupper", scope: !1268, file: !1268, line: 135, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1296 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1297, file: !1265, line: 100)
!1297 = !DISubprogram(name: "iswxdigit", scope: !1268, file: !1268, line: 140, type: !903, flags: DIFlagPrototyped, spFlags: 0)
!1298 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1299, file: !1265, line: 101)
!1299 = !DISubprogram(name: "towctrans", scope: !1262, file: !1262, line: 55, type: !1300, flags: DIFlagPrototyped, spFlags: 0)
!1300 = !DISubroutineType(types: !1301)
!1301 = !{!699, !699, !1261}
!1302 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1303, file: !1265, line: 102)
!1303 = !DISubprogram(name: "towlower", scope: !1268, file: !1268, line: 166, type: !1304, flags: DIFlagPrototyped, spFlags: 0)
!1304 = !DISubroutineType(types: !1305)
!1305 = !{!699, !699}
!1306 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1307, file: !1265, line: 103)
!1307 = !DISubprogram(name: "towupper", scope: !1268, file: !1268, line: 169, type: !1304, flags: DIFlagPrototyped, spFlags: 0)
!1308 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1309, file: !1265, line: 104)
!1309 = !DISubprogram(name: "wctrans", scope: !1262, file: !1262, line: 52, type: !1310, flags: DIFlagPrototyped, spFlags: 0)
!1310 = !DISubroutineType(types: !1311)
!1311 = !{!1261, !346}
!1312 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1313, file: !1265, line: 105)
!1313 = !DISubprogram(name: "wctype", scope: !1268, file: !1268, line: 155, type: !1314, flags: DIFlagPrototyped, spFlags: 0)
!1314 = !DISubroutineType(types: !1315)
!1315 = !{!1267, !346}
!1316 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !3, file: !1317, line: 95)
!1317 = !DIFile(filename: "/usr/lib/gcc/x86_64-linux-gnu/11/../../../../include/c++/11/bits/shared_ptr_base.h", directory: "", checksumkind: CSK_MD5, checksum: "8d23d9a03c9ca5773e092d05679e2362")
!1318 = !DIImportedEntity(tag: DW_TAG_imported_declaration, scope: !98, entity: !1319, file: !1317, line: 96)
!1319 = !DIGlobalVariable(name: "__default_lock_policy", linkageName: "_ZN9__gnu_cxxL21__default_lock_policyE", scope: !5, file: !4, line: 53, type: !1320, isLocal: true, isDefinition: false)
!1320 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !3)
!1321 = !{!"Ubuntu clang version 14.0.0-1ubuntu1.1"}
!1322 = !{i32 7, !"Dwarf Version", i32 5}
!1323 = !{i32 2, !"Debug Info Version", i32 3}
!1324 = !{i32 1, !"wchar_size", i32 4}
!1325 = !{i32 8, !"PIC Level", i32 2}
!1326 = !{i32 7, !"uwtable", i32 1}
!1327 = !{i32 7, !"frame-pointer", i32 2}
!1328 = distinct !DISubprogram(name: "raw2image_ex", linkageName: "_ZN6LibRaw12raw2image_exEi", scope: !1330, file: !1329, line: 299, type: !1332, scopeLine: 300, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, declaration: !1335, retainedNodes: !1336)
!1329 = !DIFile(filename: "LibRaw/src/preprocessing/raw2image.cpp", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729", checksumkind: CSK_MD5, checksum: "af802a14478a5835c44eef5ee293f29f")
!1330 = !DICompositeType(tag: DW_TAG_class_type, name: "LibRaw", file: !1331, line: 189, size: 6138560, flags: DIFlagFwdDecl | DIFlagNonTrivial)
!1331 = !DIFile(filename: "LibRaw/libraw/libraw.h", directory: "/home/guswjd/conexa/dataset/CVE-2023-1729", checksumkind: CSK_MD5, checksum: "a76a3196c93a90ce6546ed885783b504")
!1332 = !DISubroutineType(types: !1333)
!1333 = !{!47, !1334, !47}
!1334 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1330, size: 64, flags: DIFlagArtificial | DIFlagObjectPointer)
!1335 = !DISubprogram(name: "raw2image_ex", linkageName: "_ZN6LibRaw12raw2image_exEi", scope: !1330, file: !1331, line: 229, type: !1332, scopeLine: 229, flags: DIFlagPublic | DIFlagPrototyped, spFlags: 0)
!1336 = !{}
!1337 = !DILocalVariable(name: "this", arg: 1, scope: !1328, type: !1338, flags: DIFlagArtificial | DIFlagObjectPointer)
!1338 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1330, size: 64)
!1339 = !DILocation(line: 0, scope: !1328)
!1340 = !DILocalVariable(name: "do_subtract_black", arg: 2, scope: !1328, file: !1329, line: 299, type: !47)
!1341 = !DILocation(line: 299, column: 30, scope: !1328)
!1342 = !DILocation(line: 302, column: 3, scope: !1328)
!1343 = !DILocation(line: 302, column: 3, scope: !1344)
!1344 = distinct !DILexicalBlock(scope: !1345, file: !1329, line: 302, column: 3)
!1345 = distinct !DILexicalBlock(scope: !1328, file: !1329, line: 302, column: 3)
!1346 = !DILocation(line: 302, column: 3, scope: !1345)
!1347 = !DILocation(line: 306, column: 5, scope: !1348)
!1348 = distinct !DILexicalBlock(scope: !1328, file: !1329, line: 305, column: 3)
!1349 = !DILocation(line: 309, column: 9, scope: !1350)
!1350 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 309, column: 9)
!1351 = !DILocation(line: 309, column: 34, scope: !1350)
!1352 = !DILocation(line: 309, column: 37, scope: !1350)
!1353 = !DILocation(line: 309, column: 45, scope: !1350)
!1354 = !DILocation(line: 309, column: 53, scope: !1350)
!1355 = !DILocation(line: 309, column: 9, scope: !1348)
!1356 = !DILocation(line: 311, column: 7, scope: !1357)
!1357 = distinct !DILexicalBlock(scope: !1350, file: !1329, line: 310, column: 5)
!1358 = !DILocalVariable(name: "rc", scope: !1357, file: !1329, line: 312, type: !47)
!1359 = !DILocation(line: 312, column: 11, scope: !1357)
!1360 = !DILocation(line: 312, column: 51, scope: !1357)
!1361 = !DILocation(line: 312, column: 59, scope: !1357)
!1362 = !DILocation(line: 312, column: 67, scope: !1357)
!1363 = !DILocation(line: 312, column: 41, scope: !1357)
!1364 = !DILocation(line: 313, column: 41, scope: !1357)
!1365 = !DILocation(line: 313, column: 49, scope: !1357)
!1366 = !DILocation(line: 313, column: 57, scope: !1357)
!1367 = !DILocation(line: 312, column: 16, scope: !1357)
!1368 = !DILocation(line: 314, column: 11, scope: !1369)
!1369 = distinct !DILexicalBlock(scope: !1357, file: !1329, line: 314, column: 11)
!1370 = !DILocation(line: 314, column: 14, scope: !1369)
!1371 = !DILocation(line: 314, column: 11, scope: !1357)
!1372 = !DILocation(line: 315, column: 14, scope: !1369)
!1373 = !DILocation(line: 315, column: 12, scope: !1369)
!1374 = !DILocation(line: 315, column: 9, scope: !1369)
!1375 = !DILocation(line: 558, column: 1, scope: !1350)
!1376 = !DILocation(line: 553, column: 3, scope: !1348)
!1377 = !DILocalVariable(name: "err", scope: !1328, file: !1329, line: 554, type: !1378)
!1378 = !DIDerivedType(tag: DW_TAG_reference_type, baseType: !1379, size: 64)
!1379 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !66)
!1380 = !DILocation(line: 554, column: 35, scope: !1328)
!1381 = !DILocation(line: 556, column: 5, scope: !1382)
!1382 = distinct !DILexicalBlock(scope: !1328, file: !1329, line: 555, column: 3)
!1383 = !DILocation(line: 556, column: 5, scope: !1384)
!1384 = distinct !DILexicalBlock(scope: !1382, file: !1329, line: 556, column: 5)
!1385 = !DILocation(line: 316, column: 11, scope: !1386)
!1386 = distinct !DILexicalBlock(scope: !1357, file: !1329, line: 316, column: 11)
!1387 = !DILocation(line: 316, column: 14, scope: !1386)
!1388 = !DILocation(line: 316, column: 11, scope: !1357)
!1389 = !DILocation(line: 318, column: 9, scope: !1390)
!1390 = distinct !DILexicalBlock(scope: !1386, file: !1329, line: 317, column: 7)
!1391 = !DILocation(line: 319, column: 16, scope: !1390)
!1392 = !DILocation(line: 319, column: 9, scope: !1390)
!1393 = !DILocation(line: 321, column: 5, scope: !1357)
!1394 = !DILocalVariable(name: "do_crop", scope: !1348, file: !1329, line: 324, type: !47)
!1395 = !DILocation(line: 324, column: 9, scope: !1348)
!1396 = !DILocation(line: 325, column: 10, scope: !1397)
!1397 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 325, column: 9)
!1398 = !DILocation(line: 325, column: 12, scope: !1397)
!1399 = !DILocation(line: 325, column: 9, scope: !1397)
!1400 = !DILocation(line: 325, column: 23, scope: !1397)
!1401 = !DILocation(line: 325, column: 27, scope: !1397)
!1402 = !DILocation(line: 325, column: 29, scope: !1397)
!1403 = !DILocation(line: 325, column: 26, scope: !1397)
!1404 = !DILocation(line: 325, column: 9, scope: !1348)
!1405 = !DILocalVariable(name: "crop", scope: !1406, file: !1329, line: 327, type: !1407)
!1406 = distinct !DILexicalBlock(scope: !1397, file: !1329, line: 326, column: 5)
!1407 = !DICompositeType(tag: DW_TAG_array_type, baseType: !47, size: 128, elements: !88)
!1408 = !DILocation(line: 327, column: 11, scope: !1406)
!1409 = !DILocalVariable(name: "c", scope: !1406, file: !1329, line: 327, type: !47)
!1410 = !DILocation(line: 327, column: 20, scope: !1406)
!1411 = !DILocalVariable(name: "filt", scope: !1406, file: !1329, line: 327, type: !47)
!1412 = !DILocation(line: 327, column: 23, scope: !1406)
!1413 = !DILocalVariable(name: "q", scope: !1414, file: !1329, line: 328, type: !47)
!1414 = distinct !DILexicalBlock(scope: !1406, file: !1329, line: 328, column: 7)
!1415 = !DILocation(line: 328, column: 16, scope: !1414)
!1416 = !DILocation(line: 328, column: 12, scope: !1414)
!1417 = !DILocation(line: 328, column: 23, scope: !1418)
!1418 = distinct !DILexicalBlock(scope: !1414, file: !1329, line: 328, column: 7)
!1419 = !DILocation(line: 328, column: 25, scope: !1418)
!1420 = !DILocation(line: 328, column: 7, scope: !1414)
!1421 = !DILocation(line: 330, column: 19, scope: !1422)
!1422 = distinct !DILexicalBlock(scope: !1418, file: !1329, line: 329, column: 7)
!1423 = !DILocation(line: 330, column: 21, scope: !1422)
!1424 = !DILocation(line: 330, column: 29, scope: !1422)
!1425 = !DILocation(line: 330, column: 14, scope: !1422)
!1426 = !DILocation(line: 330, column: 9, scope: !1422)
!1427 = !DILocation(line: 330, column: 17, scope: !1422)
!1428 = !DILocation(line: 331, column: 18, scope: !1429)
!1429 = distinct !DILexicalBlock(scope: !1422, file: !1329, line: 331, column: 13)
!1430 = !DILocation(line: 331, column: 13, scope: !1429)
!1431 = !DILocation(line: 331, column: 21, scope: !1429)
!1432 = !DILocation(line: 331, column: 13, scope: !1422)
!1433 = !DILocation(line: 332, column: 16, scope: !1429)
!1434 = !DILocation(line: 332, column: 11, scope: !1429)
!1435 = !DILocation(line: 332, column: 19, scope: !1429)
!1436 = !DILocation(line: 333, column: 7, scope: !1422)
!1437 = !DILocation(line: 328, column: 31, scope: !1418)
!1438 = !DILocation(line: 328, column: 7, scope: !1418)
!1439 = distinct !{!1439, !1420, !1440, !1441}
!1440 = !DILocation(line: 333, column: 7, scope: !1414)
!1441 = !{!"llvm.loop.mustprogress"}
!1442 = !DILocation(line: 335, column: 11, scope: !1443)
!1443 = distinct !DILexicalBlock(scope: !1406, file: !1329, line: 335, column: 11)
!1444 = !DILocation(line: 335, column: 14, scope: !1443)
!1445 = !DILocation(line: 335, column: 25, scope: !1443)
!1446 = !DILocation(line: 335, column: 28, scope: !1443)
!1447 = !DILocation(line: 335, column: 36, scope: !1443)
!1448 = !DILocation(line: 335, column: 42, scope: !1443)
!1449 = !DILocation(line: 335, column: 50, scope: !1443)
!1450 = !DILocation(line: 335, column: 11, scope: !1406)
!1451 = !DILocation(line: 337, column: 20, scope: !1452)
!1452 = distinct !DILexicalBlock(scope: !1443, file: !1329, line: 336, column: 7)
!1453 = !DILocation(line: 337, column: 28, scope: !1452)
!1454 = !DILocation(line: 337, column: 33, scope: !1452)
!1455 = !DILocation(line: 337, column: 9, scope: !1452)
!1456 = !DILocation(line: 337, column: 17, scope: !1452)
!1457 = !DILocation(line: 338, column: 20, scope: !1452)
!1458 = !DILocation(line: 338, column: 28, scope: !1452)
!1459 = !DILocation(line: 338, column: 33, scope: !1452)
!1460 = !DILocation(line: 338, column: 9, scope: !1452)
!1461 = !DILocation(line: 338, column: 17, scope: !1452)
!1462 = !DILocation(line: 339, column: 14, scope: !1463)
!1463 = distinct !DILexicalBlock(scope: !1452, file: !1329, line: 339, column: 13)
!1464 = !DILocation(line: 339, column: 35, scope: !1463)
!1465 = !DILocation(line: 339, column: 49, scope: !1463)
!1466 = !DILocation(line: 339, column: 13, scope: !1452)
!1467 = !DILocation(line: 341, column: 22, scope: !1468)
!1468 = distinct !DILexicalBlock(scope: !1463, file: !1329, line: 340, column: 9)
!1469 = !DILocation(line: 341, column: 11, scope: !1468)
!1470 = !DILocation(line: 341, column: 19, scope: !1468)
!1471 = !DILocation(line: 342, column: 22, scope: !1468)
!1472 = !DILocation(line: 342, column: 11, scope: !1468)
!1473 = !DILocation(line: 342, column: 19, scope: !1468)
!1474 = !DILocation(line: 343, column: 9, scope: !1468)
!1475 = !DILocation(line: 344, column: 20, scope: !1452)
!1476 = !DILocation(line: 344, column: 28, scope: !1452)
!1477 = !DILocation(line: 344, column: 32, scope: !1452)
!1478 = !DILocation(line: 344, column: 37, scope: !1452)
!1479 = !DILocation(line: 344, column: 9, scope: !1452)
!1480 = !DILocation(line: 344, column: 17, scope: !1452)
!1481 = !DILocation(line: 345, column: 20, scope: !1452)
!1482 = !DILocation(line: 345, column: 28, scope: !1452)
!1483 = !DILocation(line: 345, column: 32, scope: !1452)
!1484 = !DILocation(line: 345, column: 37, scope: !1452)
!1485 = !DILocation(line: 345, column: 9, scope: !1452)
!1486 = !DILocation(line: 345, column: 17, scope: !1452)
!1487 = !DILocation(line: 346, column: 7, scope: !1452)
!1488 = !DILocation(line: 347, column: 16, scope: !1489)
!1489 = distinct !DILexicalBlock(scope: !1443, file: !1329, line: 347, column: 16)
!1490 = !DILocation(line: 347, column: 24, scope: !1489)
!1491 = !DILocation(line: 347, column: 30, scope: !1489)
!1492 = !DILocation(line: 347, column: 38, scope: !1489)
!1493 = !DILocation(line: 347, column: 16, scope: !1443)
!1494 = !DILocation(line: 349, column: 20, scope: !1495)
!1495 = distinct !DILexicalBlock(scope: !1489, file: !1329, line: 348, column: 7)
!1496 = !DILocation(line: 349, column: 28, scope: !1495)
!1497 = !DILocation(line: 349, column: 34, scope: !1495)
!1498 = !DILocation(line: 349, column: 9, scope: !1495)
!1499 = !DILocation(line: 349, column: 17, scope: !1495)
!1500 = !DILocation(line: 350, column: 20, scope: !1495)
!1501 = !DILocation(line: 350, column: 28, scope: !1495)
!1502 = !DILocation(line: 350, column: 34, scope: !1495)
!1503 = !DILocation(line: 350, column: 9, scope: !1495)
!1504 = !DILocation(line: 350, column: 17, scope: !1495)
!1505 = !DILocation(line: 351, column: 7, scope: !1495)
!1506 = !DILocation(line: 352, column: 16, scope: !1507)
!1507 = distinct !DILexicalBlock(scope: !1489, file: !1329, line: 352, column: 16)
!1508 = !DILocation(line: 352, column: 24, scope: !1507)
!1509 = !DILocation(line: 352, column: 30, scope: !1507)
!1510 = !DILocation(line: 352, column: 38, scope: !1507)
!1511 = !DILocation(line: 352, column: 16, scope: !1489)
!1512 = !DILocation(line: 354, column: 20, scope: !1513)
!1513 = distinct !DILexicalBlock(scope: !1507, file: !1329, line: 353, column: 7)
!1514 = !DILocation(line: 354, column: 28, scope: !1513)
!1515 = !DILocation(line: 354, column: 33, scope: !1513)
!1516 = !DILocation(line: 354, column: 9, scope: !1513)
!1517 = !DILocation(line: 354, column: 17, scope: !1513)
!1518 = !DILocation(line: 355, column: 20, scope: !1513)
!1519 = !DILocation(line: 355, column: 28, scope: !1513)
!1520 = !DILocation(line: 355, column: 33, scope: !1513)
!1521 = !DILocation(line: 355, column: 9, scope: !1513)
!1522 = !DILocation(line: 355, column: 17, scope: !1513)
!1523 = !DILocation(line: 356, column: 7, scope: !1513)
!1524 = !DILocation(line: 357, column: 15, scope: !1406)
!1525 = !DILocation(line: 359, column: 17, scope: !1406)
!1526 = !DILocation(line: 359, column: 7, scope: !1406)
!1527 = !DILocation(line: 359, column: 15, scope: !1406)
!1528 = !DILocation(line: 360, column: 17, scope: !1406)
!1529 = !DILocation(line: 360, column: 7, scope: !1406)
!1530 = !DILocation(line: 360, column: 15, scope: !1406)
!1531 = !DILocation(line: 361, column: 11, scope: !1532)
!1532 = distinct !DILexicalBlock(scope: !1406, file: !1329, line: 361, column: 11)
!1533 = !DILocation(line: 361, column: 19, scope: !1532)
!1534 = !DILocation(line: 361, column: 24, scope: !1532)
!1535 = !DILocation(line: 361, column: 27, scope: !1532)
!1536 = !DILocation(line: 361, column: 35, scope: !1532)
!1537 = !DILocation(line: 361, column: 11, scope: !1406)
!1538 = !DILocation(line: 362, column: 9, scope: !1532)
!1539 = !DILocation(line: 365, column: 24, scope: !1406)
!1540 = !DILocation(line: 365, column: 7, scope: !1406)
!1541 = !DILocation(line: 365, column: 9, scope: !1406)
!1542 = !DILocation(line: 365, column: 21, scope: !1406)
!1543 = !DILocation(line: 366, column: 23, scope: !1406)
!1544 = !DILocation(line: 366, column: 7, scope: !1406)
!1545 = !DILocation(line: 366, column: 9, scope: !1406)
!1546 = !DILocation(line: 366, column: 20, scope: !1406)
!1547 = !DILocation(line: 367, column: 17, scope: !1406)
!1548 = !DILocation(line: 367, column: 7, scope: !1406)
!1549 = !DILocation(line: 367, column: 9, scope: !1406)
!1550 = !DILocation(line: 367, column: 15, scope: !1406)
!1551 = !DILocation(line: 368, column: 18, scope: !1406)
!1552 = !DILocation(line: 368, column: 7, scope: !1406)
!1553 = !DILocation(line: 368, column: 9, scope: !1406)
!1554 = !DILocation(line: 368, column: 16, scope: !1406)
!1555 = !DILocation(line: 370, column: 20, scope: !1406)
!1556 = !DILocation(line: 370, column: 22, scope: !1406)
!1557 = !DILocation(line: 370, column: 31, scope: !1406)
!1558 = !DILocation(line: 370, column: 34, scope: !1406)
!1559 = !DILocation(line: 370, column: 29, scope: !1406)
!1560 = !DILocation(line: 370, column: 45, scope: !1406)
!1561 = !DILocation(line: 370, column: 48, scope: !1406)
!1562 = !DILocation(line: 370, column: 42, scope: !1406)
!1563 = !DILocation(line: 370, column: 19, scope: !1406)
!1564 = !DILocation(line: 370, column: 7, scope: !1406)
!1565 = !DILocation(line: 370, column: 9, scope: !1406)
!1566 = !DILocation(line: 370, column: 17, scope: !1406)
!1567 = !DILocation(line: 371, column: 19, scope: !1406)
!1568 = !DILocation(line: 371, column: 21, scope: !1406)
!1569 = !DILocation(line: 371, column: 29, scope: !1406)
!1570 = !DILocation(line: 371, column: 32, scope: !1406)
!1571 = !DILocation(line: 371, column: 27, scope: !1406)
!1572 = !DILocation(line: 371, column: 43, scope: !1406)
!1573 = !DILocation(line: 371, column: 46, scope: !1406)
!1574 = !DILocation(line: 371, column: 40, scope: !1406)
!1575 = !DILocation(line: 371, column: 18, scope: !1406)
!1576 = !DILocation(line: 371, column: 7, scope: !1406)
!1577 = !DILocation(line: 371, column: 9, scope: !1406)
!1578 = !DILocation(line: 371, column: 16, scope: !1406)
!1579 = !DILocation(line: 372, column: 12, scope: !1580)
!1580 = distinct !DILexicalBlock(scope: !1406, file: !1329, line: 372, column: 11)
!1581 = !DILocation(line: 372, column: 15, scope: !1580)
!1582 = !DILocation(line: 372, column: 26, scope: !1580)
!1583 = !DILocation(line: 372, column: 29, scope: !1580)
!1584 = !DILocation(line: 372, column: 37, scope: !1580)
!1585 = !DILocation(line: 372, column: 43, scope: !1580)
!1586 = !DILocation(line: 372, column: 51, scope: !1580)
!1587 = !DILocation(line: 373, column: 11, scope: !1580)
!1588 = !DILocation(line: 373, column: 19, scope: !1580)
!1589 = !DILocation(line: 373, column: 25, scope: !1580)
!1590 = !DILocation(line: 373, column: 33, scope: !1580)
!1591 = !DILocation(line: 372, column: 11, scope: !1406)
!1592 = !DILocation(line: 375, column: 23, scope: !1593)
!1593 = distinct !DILexicalBlock(scope: !1594, file: !1329, line: 375, column: 9)
!1594 = distinct !DILexicalBlock(scope: !1580, file: !1329, line: 374, column: 7)
!1595 = !DILocation(line: 375, column: 19, scope: !1593)
!1596 = !DILocation(line: 375, column: 14, scope: !1593)
!1597 = !DILocation(line: 375, column: 28, scope: !1598)
!1598 = distinct !DILexicalBlock(scope: !1593, file: !1329, line: 375, column: 9)
!1599 = !DILocation(line: 375, column: 30, scope: !1598)
!1600 = !DILocation(line: 375, column: 9, scope: !1593)
!1601 = !DILocation(line: 376, column: 23, scope: !1598)
!1602 = !DILocation(line: 376, column: 25, scope: !1598)
!1603 = !DILocation(line: 376, column: 34, scope: !1598)
!1604 = !DILocation(line: 376, column: 31, scope: !1598)
!1605 = !DILocation(line: 376, column: 45, scope: !1598)
!1606 = !DILocation(line: 376, column: 47, scope: !1598)
!1607 = !DILocation(line: 376, column: 55, scope: !1598)
!1608 = !DILocation(line: 376, column: 52, scope: !1598)
!1609 = !DILocation(line: 376, column: 19, scope: !1598)
!1610 = !DILocation(line: 376, column: 68, scope: !1598)
!1611 = !DILocation(line: 376, column: 70, scope: !1598)
!1612 = !DILocation(line: 376, column: 65, scope: !1598)
!1613 = !DILocation(line: 376, column: 16, scope: !1598)
!1614 = !DILocation(line: 376, column: 11, scope: !1598)
!1615 = !DILocation(line: 375, column: 37, scope: !1598)
!1616 = !DILocation(line: 375, column: 9, scope: !1598)
!1617 = distinct !{!1617, !1600, !1618, !1441}
!1618 = !DILocation(line: 376, column: 72, scope: !1593)
!1619 = !DILocation(line: 377, column: 33, scope: !1594)
!1620 = !DILocation(line: 377, column: 9, scope: !1594)
!1621 = !DILocation(line: 377, column: 17, scope: !1594)
!1622 = !DILocation(line: 377, column: 23, scope: !1594)
!1623 = !DILocation(line: 377, column: 31, scope: !1594)
!1624 = !DILocation(line: 378, column: 7, scope: !1594)
!1625 = !DILocation(line: 379, column: 5, scope: !1406)
!1626 = !DILocalVariable(name: "alloc_width", scope: !1348, file: !1329, line: 381, type: !47)
!1627 = !DILocation(line: 381, column: 9, scope: !1348)
!1628 = !DILocation(line: 381, column: 23, scope: !1348)
!1629 = !DILocation(line: 381, column: 25, scope: !1348)
!1630 = !DILocalVariable(name: "alloc_height", scope: !1348, file: !1329, line: 382, type: !47)
!1631 = !DILocation(line: 382, column: 9, scope: !1348)
!1632 = !DILocation(line: 382, column: 24, scope: !1348)
!1633 = !DILocation(line: 382, column: 26, scope: !1348)
!1634 = !DILocation(line: 384, column: 9, scope: !1635)
!1635 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 384, column: 9)
!1636 = !DILocation(line: 384, column: 12, scope: !1635)
!1637 = !DILocation(line: 384, column: 23, scope: !1635)
!1638 = !DILocation(line: 384, column: 26, scope: !1635)
!1639 = !DILocation(line: 384, column: 9, scope: !1348)
!1640 = !DILocalVariable(name: "IO_fw", scope: !1641, file: !1329, line: 386, type: !47)
!1641 = distinct !DILexicalBlock(scope: !1635, file: !1329, line: 385, column: 5)
!1642 = !DILocation(line: 386, column: 11, scope: !1641)
!1643 = !DILocation(line: 386, column: 19, scope: !1641)
!1644 = !DILocation(line: 386, column: 21, scope: !1641)
!1645 = !DILocation(line: 386, column: 35, scope: !1641)
!1646 = !DILocation(line: 386, column: 56, scope: !1641)
!1647 = !DILocation(line: 386, column: 70, scope: !1641)
!1648 = !DILocation(line: 386, column: 34, scope: !1641)
!1649 = !DILocation(line: 386, column: 27, scope: !1641)
!1650 = !DILocalVariable(name: "t_alloc_width", scope: !1641, file: !1329, line: 387, type: !47)
!1651 = !DILocation(line: 387, column: 11, scope: !1641)
!1652 = !DILocation(line: 388, column: 12, scope: !1641)
!1653 = !DILocation(line: 388, column: 14, scope: !1641)
!1654 = !DILocation(line: 388, column: 24, scope: !1641)
!1655 = !DILocation(line: 388, column: 45, scope: !1641)
!1656 = !DILocation(line: 388, column: 59, scope: !1641)
!1657 = !DILocation(line: 388, column: 21, scope: !1641)
!1658 = !DILocation(line: 388, column: 74, scope: !1641)
!1659 = !DILocation(line: 388, column: 72, scope: !1641)
!1660 = !DILocalVariable(name: "t_alloc_height", scope: !1641, file: !1329, line: 389, type: !47)
!1661 = !DILocation(line: 389, column: 11, scope: !1641)
!1662 = !DILocation(line: 389, column: 28, scope: !1641)
!1663 = !DILocation(line: 389, column: 42, scope: !1641)
!1664 = !DILocation(line: 390, column: 23, scope: !1641)
!1665 = !DILocation(line: 390, column: 40, scope: !1641)
!1666 = !DILocation(line: 390, column: 43, scope: !1641)
!1667 = !DILocation(line: 390, column: 38, scope: !1641)
!1668 = !DILocation(line: 390, column: 54, scope: !1641)
!1669 = !DILocation(line: 390, column: 57, scope: !1641)
!1670 = !DILocation(line: 390, column: 51, scope: !1641)
!1671 = !DILocation(line: 390, column: 20, scope: !1641)
!1672 = !DILocation(line: 391, column: 22, scope: !1641)
!1673 = !DILocation(line: 391, column: 38, scope: !1641)
!1674 = !DILocation(line: 391, column: 41, scope: !1641)
!1675 = !DILocation(line: 391, column: 36, scope: !1641)
!1676 = !DILocation(line: 391, column: 52, scope: !1641)
!1677 = !DILocation(line: 391, column: 55, scope: !1641)
!1678 = !DILocation(line: 391, column: 49, scope: !1641)
!1679 = !DILocation(line: 391, column: 19, scope: !1641)
!1680 = !DILocation(line: 392, column: 5, scope: !1641)
!1681 = !DILocalVariable(name: "alloc_sz", scope: !1348, file: !1329, line: 393, type: !47)
!1682 = !DILocation(line: 393, column: 9, scope: !1348)
!1683 = !DILocation(line: 393, column: 20, scope: !1348)
!1684 = !DILocation(line: 393, column: 34, scope: !1348)
!1685 = !DILocation(line: 393, column: 32, scope: !1348)
!1686 = !DILocation(line: 395, column: 9, scope: !1687)
!1687 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 395, column: 9)
!1688 = !DILocation(line: 395, column: 17, scope: !1687)
!1689 = !DILocation(line: 395, column: 9, scope: !1348)
!1690 = !DILocation(line: 397, column: 45, scope: !1691)
!1691 = distinct !DILexicalBlock(scope: !1687, file: !1329, line: 396, column: 5)
!1692 = !DILocation(line: 397, column: 53, scope: !1691)
!1693 = !DILocation(line: 398, column: 45, scope: !1691)
!1694 = !DILocation(line: 398, column: 54, scope: !1691)
!1695 = !DILocation(line: 397, column: 37, scope: !1691)
!1696 = !DILocation(line: 397, column: 23, scope: !1691)
!1697 = !DILocation(line: 397, column: 7, scope: !1691)
!1698 = !DILocation(line: 397, column: 15, scope: !1691)
!1699 = !DILocation(line: 397, column: 21, scope: !1691)
!1700 = !DILocation(line: 399, column: 14, scope: !1691)
!1701 = !DILocation(line: 399, column: 22, scope: !1691)
!1702 = !DILocation(line: 399, column: 7, scope: !1691)
!1703 = !DILocation(line: 399, column: 32, scope: !1691)
!1704 = !DILocation(line: 399, column: 41, scope: !1691)
!1705 = !DILocation(line: 400, column: 5, scope: !1691)
!1706 = !DILocation(line: 402, column: 44, scope: !1687)
!1707 = !DILocation(line: 402, column: 37, scope: !1687)
!1708 = !DILocation(line: 402, column: 23, scope: !1687)
!1709 = !DILocation(line: 402, column: 7, scope: !1687)
!1710 = !DILocation(line: 402, column: 15, scope: !1687)
!1711 = !DILocation(line: 402, column: 21, scope: !1687)
!1712 = !DILocalVariable(name: "decoder_info", scope: !1348, file: !1329, line: 404, type: !1713)
!1713 = !DIDerivedType(tag: DW_TAG_typedef, name: "libraw_decoder_info_t", file: !84, line: 124, baseType: !1714)
!1714 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !84, line: 120, size: 128, flags: DIFlagTypePassByValue, elements: !1715, identifier: "_ZTS21libraw_decoder_info_t")
!1715 = !{!1716, !1717}
!1716 = !DIDerivedType(tag: DW_TAG_member, name: "decoder_name", scope: !1714, file: !84, line: 122, baseType: !346, size: 64)
!1717 = !DIDerivedType(tag: DW_TAG_member, name: "decoder_flags", scope: !1714, file: !84, line: 123, baseType: !6, size: 32, offset: 64)
!1718 = !DILocation(line: 404, column: 27, scope: !1348)
!1719 = !DILocation(line: 405, column: 5, scope: !1348)
!1720 = !DILocalVariable(name: "cblack", scope: !1348, file: !1329, line: 408, type: !1721)
!1721 = !DICompositeType(tag: DW_TAG_array_type, baseType: !85, size: 64, elements: !88)
!1722 = !DILocation(line: 408, column: 20, scope: !1348)
!1723 = !DILocalVariable(name: "dmax", scope: !1348, file: !1329, line: 409, type: !85)
!1724 = !DILocation(line: 409, column: 20, scope: !1348)
!1725 = !DILocation(line: 410, column: 9, scope: !1726)
!1726 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 410, column: 9)
!1727 = !DILocation(line: 410, column: 9, scope: !1348)
!1728 = !DILocation(line: 412, column: 7, scope: !1729)
!1729 = distinct !DILexicalBlock(scope: !1726, file: !1329, line: 411, column: 5)
!1730 = !DILocalVariable(name: "i", scope: !1731, file: !1329, line: 413, type: !47)
!1731 = distinct !DILexicalBlock(scope: !1729, file: !1329, line: 413, column: 7)
!1732 = !DILocation(line: 413, column: 16, scope: !1731)
!1733 = !DILocation(line: 413, column: 12, scope: !1731)
!1734 = !DILocation(line: 413, column: 23, scope: !1735)
!1735 = distinct !DILexicalBlock(scope: !1731, file: !1329, line: 413, column: 7)
!1736 = !DILocation(line: 413, column: 25, scope: !1735)
!1737 = !DILocation(line: 413, column: 7, scope: !1731)
!1738 = !DILocation(line: 414, column: 37, scope: !1735)
!1739 = !DILocation(line: 414, column: 39, scope: !1735)
!1740 = !DILocation(line: 414, column: 46, scope: !1735)
!1741 = !DILocation(line: 414, column: 16, scope: !1735)
!1742 = !DILocation(line: 414, column: 9, scope: !1735)
!1743 = !DILocation(line: 414, column: 19, scope: !1735)
!1744 = !DILocation(line: 413, column: 31, scope: !1735)
!1745 = !DILocation(line: 413, column: 7, scope: !1735)
!1746 = distinct !{!1746, !1737, !1747, !1441}
!1747 = !DILocation(line: 414, column: 47, scope: !1731)
!1748 = !DILocation(line: 415, column: 5, scope: !1729)
!1749 = !DILocalVariable(name: "copyheight", scope: !1348, file: !1329, line: 418, type: !47)
!1750 = !DILocation(line: 418, column: 9, scope: !1348)
!1751 = !DILocation(line: 418, column: 22, scope: !1348)
!1752 = !DILocalVariable(name: "copywidth", scope: !1348, file: !1329, line: 419, type: !47)
!1753 = !DILocation(line: 419, column: 9, scope: !1348)
!1754 = !DILocation(line: 419, column: 21, scope: !1348)
!1755 = !DILocation(line: 422, column: 10, scope: !1756)
!1756 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 422, column: 9)
!1757 = !DILocation(line: 422, column: 18, scope: !1756)
!1758 = !DILocation(line: 422, column: 24, scope: !1756)
!1759 = !DILocation(line: 422, column: 32, scope: !1756)
!1760 = !DILocation(line: 422, column: 35, scope: !1756)
!1761 = !DILocation(line: 422, column: 38, scope: !1756)
!1762 = !DILocation(line: 422, column: 45, scope: !1756)
!1763 = !DILocation(line: 422, column: 51, scope: !1756)
!1764 = !DILocation(line: 422, column: 54, scope: !1756)
!1765 = !DILocation(line: 422, column: 62, scope: !1756)
!1766 = !DILocation(line: 422, column: 70, scope: !1756)
!1767 = !DILocation(line: 422, column: 9, scope: !1348)
!1768 = !DILocation(line: 424, column: 11, scope: !1769)
!1769 = distinct !DILexicalBlock(scope: !1770, file: !1329, line: 424, column: 11)
!1770 = distinct !DILexicalBlock(scope: !1756, file: !1329, line: 423, column: 5)
!1771 = !DILocation(line: 424, column: 14, scope: !1769)
!1772 = !DILocation(line: 424, column: 11, scope: !1770)
!1773 = !DILocation(line: 426, column: 13, scope: !1774)
!1774 = distinct !DILexicalBlock(scope: !1775, file: !1329, line: 426, column: 13)
!1775 = distinct !DILexicalBlock(scope: !1769, file: !1329, line: 425, column: 7)
!1776 = !DILocation(line: 426, column: 13, scope: !1775)
!1777 = !DILocation(line: 429, column: 15, scope: !1778)
!1778 = distinct !DILexicalBlock(scope: !1774, file: !1329, line: 427, column: 9)
!1779 = !DILocation(line: 429, column: 17, scope: !1778)
!1780 = !DILocation(line: 429, column: 31, scope: !1778)
!1781 = !DILocation(line: 429, column: 52, scope: !1778)
!1782 = !DILocation(line: 429, column: 66, scope: !1778)
!1783 = !DILocation(line: 429, column: 30, scope: !1778)
!1784 = !DILocation(line: 429, column: 23, scope: !1778)
!1785 = !DILocation(line: 428, column: 11, scope: !1778)
!1786 = !DILocation(line: 428, column: 14, scope: !1778)
!1787 = !DILocation(line: 428, column: 25, scope: !1778)
!1788 = !DILocalVariable(name: "IO_fwidth", scope: !1778, file: !1329, line: 430, type: !47)
!1789 = !DILocation(line: 430, column: 15, scope: !1778)
!1790 = !DILocation(line: 431, column: 16, scope: !1778)
!1791 = !DILocation(line: 431, column: 18, scope: !1778)
!1792 = !DILocation(line: 431, column: 32, scope: !1778)
!1793 = !DILocation(line: 431, column: 53, scope: !1778)
!1794 = !DILocation(line: 431, column: 67, scope: !1778)
!1795 = !DILocation(line: 431, column: 25, scope: !1778)
!1796 = !DILocation(line: 432, column: 15, scope: !1778)
!1797 = !DILocation(line: 432, column: 18, scope: !1778)
!1798 = !DILocation(line: 431, column: 81, scope: !1778)
!1799 = !DILocalVariable(name: "IO_fheight", scope: !1778, file: !1329, line: 433, type: !47)
!1800 = !DILocation(line: 433, column: 15, scope: !1778)
!1801 = !DILocation(line: 433, column: 28, scope: !1778)
!1802 = !DILocation(line: 433, column: 38, scope: !1778)
!1803 = !DILocalVariable(name: "row", scope: !1778, file: !1329, line: 435, type: !47)
!1804 = !DILocation(line: 435, column: 15, scope: !1778)
!1805 = !DILocalVariable(name: "col", scope: !1778, file: !1329, line: 435, type: !47)
!1806 = !DILocation(line: 435, column: 20, scope: !1778)
!1807 = !DILocation(line: 436, column: 20, scope: !1808)
!1808 = distinct !DILexicalBlock(scope: !1778, file: !1329, line: 436, column: 11)
!1809 = !DILocation(line: 436, column: 16, scope: !1808)
!1810 = !DILocation(line: 436, column: 25, scope: !1811)
!1811 = distinct !DILexicalBlock(scope: !1808, file: !1329, line: 436, column: 11)
!1812 = !DILocation(line: 436, column: 31, scope: !1811)
!1813 = !DILocation(line: 436, column: 33, scope: !1811)
!1814 = !DILocation(line: 436, column: 29, scope: !1811)
!1815 = !DILocation(line: 436, column: 11, scope: !1808)
!1816 = !DILocation(line: 438, column: 22, scope: !1817)
!1817 = distinct !DILexicalBlock(scope: !1818, file: !1329, line: 438, column: 13)
!1818 = distinct !DILexicalBlock(scope: !1811, file: !1329, line: 437, column: 11)
!1819 = !DILocation(line: 438, column: 18, scope: !1817)
!1820 = !DILocation(line: 438, column: 27, scope: !1821)
!1821 = distinct !DILexicalBlock(scope: !1817, file: !1329, line: 438, column: 13)
!1822 = !DILocation(line: 438, column: 33, scope: !1821)
!1823 = !DILocation(line: 438, column: 35, scope: !1821)
!1824 = !DILocation(line: 438, column: 31, scope: !1821)
!1825 = !DILocation(line: 438, column: 13, scope: !1817)
!1826 = !DILocalVariable(name: "r", scope: !1827, file: !1329, line: 440, type: !47)
!1827 = distinct !DILexicalBlock(scope: !1821, file: !1329, line: 439, column: 13)
!1828 = !DILocation(line: 440, column: 19, scope: !1827)
!1829 = !DILocalVariable(name: "c", scope: !1827, file: !1329, line: 440, type: !47)
!1830 = !DILocation(line: 440, column: 22, scope: !1827)
!1831 = !DILocation(line: 441, column: 19, scope: !1832)
!1832 = distinct !DILexicalBlock(scope: !1827, file: !1329, line: 441, column: 19)
!1833 = !DILocation(line: 441, column: 40, scope: !1832)
!1834 = !DILocation(line: 441, column: 54, scope: !1832)
!1835 = !DILocation(line: 441, column: 19, scope: !1827)
!1836 = !DILocation(line: 443, column: 21, scope: !1837)
!1837 = distinct !DILexicalBlock(scope: !1832, file: !1329, line: 442, column: 15)
!1838 = !DILocation(line: 443, column: 24, scope: !1837)
!1839 = !DILocation(line: 443, column: 35, scope: !1837)
!1840 = !DILocation(line: 443, column: 41, scope: !1837)
!1841 = !DILocation(line: 443, column: 39, scope: !1837)
!1842 = !DILocation(line: 443, column: 48, scope: !1837)
!1843 = !DILocation(line: 443, column: 52, scope: !1837)
!1844 = !DILocation(line: 443, column: 45, scope: !1837)
!1845 = !DILocation(line: 443, column: 19, scope: !1837)
!1846 = !DILocation(line: 444, column: 21, scope: !1837)
!1847 = !DILocation(line: 444, column: 29, scope: !1837)
!1848 = !DILocation(line: 444, column: 33, scope: !1837)
!1849 = !DILocation(line: 444, column: 38, scope: !1837)
!1850 = !DILocation(line: 444, column: 25, scope: !1837)
!1851 = !DILocation(line: 444, column: 19, scope: !1837)
!1852 = !DILocation(line: 445, column: 15, scope: !1837)
!1853 = !DILocation(line: 448, column: 21, scope: !1854)
!1854 = distinct !DILexicalBlock(scope: !1832, file: !1329, line: 447, column: 15)
!1855 = !DILocation(line: 448, column: 24, scope: !1854)
!1856 = !DILocation(line: 448, column: 35, scope: !1854)
!1857 = !DILocation(line: 448, column: 41, scope: !1854)
!1858 = !DILocation(line: 448, column: 39, scope: !1854)
!1859 = !DILocation(line: 448, column: 48, scope: !1854)
!1860 = !DILocation(line: 448, column: 52, scope: !1854)
!1861 = !DILocation(line: 448, column: 45, scope: !1854)
!1862 = !DILocation(line: 448, column: 19, scope: !1854)
!1863 = !DILocation(line: 449, column: 21, scope: !1854)
!1864 = !DILocation(line: 449, column: 29, scope: !1854)
!1865 = !DILocation(line: 449, column: 33, scope: !1854)
!1866 = !DILocation(line: 449, column: 38, scope: !1854)
!1867 = !DILocation(line: 449, column: 25, scope: !1854)
!1868 = !DILocation(line: 449, column: 19, scope: !1854)
!1869 = !DILocalVariable(name: "val", scope: !1827, file: !1329, line: 452, type: !85)
!1870 = !DILocation(line: 452, column: 30, scope: !1827)
!1871 = !DILocation(line: 453, column: 19, scope: !1827)
!1872 = !DILocation(line: 453, column: 27, scope: !1827)
!1873 = !DILocation(line: 454, column: 24, scope: !1827)
!1874 = !DILocation(line: 454, column: 35, scope: !1827)
!1875 = !DILocation(line: 454, column: 41, scope: !1827)
!1876 = !DILocation(line: 454, column: 43, scope: !1827)
!1877 = !DILocation(line: 454, column: 39, scope: !1827)
!1878 = !DILocation(line: 454, column: 57, scope: !1827)
!1879 = !DILocation(line: 454, column: 59, scope: !1827)
!1880 = !DILocation(line: 454, column: 55, scope: !1827)
!1881 = !DILocation(line: 454, column: 69, scope: !1827)
!1882 = !DILocation(line: 455, column: 35, scope: !1827)
!1883 = !DILocation(line: 455, column: 41, scope: !1827)
!1884 = !DILocation(line: 455, column: 43, scope: !1827)
!1885 = !DILocation(line: 455, column: 39, scope: !1827)
!1886 = !DILocation(line: 454, column: 73, scope: !1827)
!1887 = !DILocalVariable(name: "cc", scope: !1827, file: !1329, line: 456, type: !47)
!1888 = !DILocation(line: 456, column: 19, scope: !1827)
!1889 = !DILocation(line: 456, column: 28, scope: !1827)
!1890 = !DILocation(line: 456, column: 33, scope: !1827)
!1891 = !DILocation(line: 456, column: 24, scope: !1827)
!1892 = !DILocation(line: 457, column: 19, scope: !1893)
!1893 = distinct !DILexicalBlock(scope: !1827, file: !1329, line: 457, column: 19)
!1894 = !DILocation(line: 457, column: 32, scope: !1893)
!1895 = !DILocation(line: 457, column: 25, scope: !1893)
!1896 = !DILocation(line: 457, column: 23, scope: !1893)
!1897 = !DILocation(line: 457, column: 19, scope: !1827)
!1898 = !DILocation(line: 459, column: 31, scope: !1899)
!1899 = distinct !DILexicalBlock(scope: !1893, file: !1329, line: 458, column: 15)
!1900 = !DILocation(line: 459, column: 24, scope: !1899)
!1901 = !DILocation(line: 459, column: 21, scope: !1899)
!1902 = !DILocation(line: 460, column: 21, scope: !1903)
!1903 = distinct !DILexicalBlock(scope: !1899, file: !1329, line: 460, column: 21)
!1904 = !DILocation(line: 460, column: 28, scope: !1903)
!1905 = !DILocation(line: 460, column: 26, scope: !1903)
!1906 = !DILocation(line: 460, column: 21, scope: !1899)
!1907 = !DILocation(line: 461, column: 26, scope: !1903)
!1908 = !DILocation(line: 461, column: 24, scope: !1903)
!1909 = !DILocation(line: 461, column: 19, scope: !1903)
!1910 = !DILocation(line: 462, column: 15, scope: !1899)
!1911 = !DILocation(line: 464, column: 21, scope: !1893)
!1912 = !DILocation(line: 466, column: 55, scope: !1827)
!1913 = !DILocation(line: 465, column: 15, scope: !1827)
!1914 = !DILocation(line: 465, column: 23, scope: !1827)
!1915 = !DILocation(line: 465, column: 31, scope: !1827)
!1916 = !DILocation(line: 465, column: 37, scope: !1827)
!1917 = !DILocation(line: 465, column: 40, scope: !1827)
!1918 = !DILocation(line: 465, column: 34, scope: !1827)
!1919 = !DILocation(line: 465, column: 50, scope: !1827)
!1920 = !DILocation(line: 465, column: 48, scope: !1827)
!1921 = !DILocation(line: 466, column: 31, scope: !1827)
!1922 = !DILocation(line: 466, column: 37, scope: !1827)
!1923 = !DILocation(line: 466, column: 40, scope: !1827)
!1924 = !DILocation(line: 466, column: 34, scope: !1827)
!1925 = !DILocation(line: 465, column: 62, scope: !1827)
!1926 = !DILocation(line: 466, column: 49, scope: !1827)
!1927 = !DILocation(line: 466, column: 53, scope: !1827)
!1928 = !DILocation(line: 467, column: 13, scope: !1827)
!1929 = !DILocation(line: 438, column: 45, scope: !1821)
!1930 = !DILocation(line: 438, column: 13, scope: !1821)
!1931 = distinct !{!1931, !1825, !1932, !1441}
!1932 = !DILocation(line: 467, column: 13, scope: !1817)
!1933 = !DILocation(line: 468, column: 11, scope: !1818)
!1934 = !DILocation(line: 436, column: 44, scope: !1811)
!1935 = !DILocation(line: 436, column: 11, scope: !1811)
!1936 = distinct !{!1936, !1815, !1937, !1441}
!1937 = !DILocation(line: 468, column: 11, scope: !1808)
!1938 = !DILocation(line: 469, column: 22, scope: !1778)
!1939 = !DILocation(line: 469, column: 11, scope: !1778)
!1940 = !DILocation(line: 469, column: 13, scope: !1778)
!1941 = !DILocation(line: 469, column: 20, scope: !1778)
!1942 = !DILocation(line: 470, column: 21, scope: !1778)
!1943 = !DILocation(line: 470, column: 11, scope: !1778)
!1944 = !DILocation(line: 470, column: 13, scope: !1778)
!1945 = !DILocation(line: 470, column: 19, scope: !1778)
!1946 = !DILocation(line: 471, column: 24, scope: !1778)
!1947 = !DILocation(line: 471, column: 26, scope: !1778)
!1948 = !DILocation(line: 471, column: 35, scope: !1778)
!1949 = !DILocation(line: 471, column: 38, scope: !1778)
!1950 = !DILocation(line: 471, column: 33, scope: !1778)
!1951 = !DILocation(line: 471, column: 49, scope: !1778)
!1952 = !DILocation(line: 471, column: 52, scope: !1778)
!1953 = !DILocation(line: 471, column: 46, scope: !1778)
!1954 = !DILocation(line: 471, column: 23, scope: !1778)
!1955 = !DILocation(line: 471, column: 11, scope: !1778)
!1956 = !DILocation(line: 471, column: 13, scope: !1778)
!1957 = !DILocation(line: 471, column: 21, scope: !1778)
!1958 = !DILocation(line: 472, column: 23, scope: !1778)
!1959 = !DILocation(line: 472, column: 25, scope: !1778)
!1960 = !DILocation(line: 472, column: 33, scope: !1778)
!1961 = !DILocation(line: 472, column: 36, scope: !1778)
!1962 = !DILocation(line: 472, column: 31, scope: !1778)
!1963 = !DILocation(line: 472, column: 47, scope: !1778)
!1964 = !DILocation(line: 472, column: 50, scope: !1778)
!1965 = !DILocation(line: 472, column: 44, scope: !1778)
!1966 = !DILocation(line: 472, column: 22, scope: !1778)
!1967 = !DILocation(line: 472, column: 11, scope: !1778)
!1968 = !DILocation(line: 472, column: 13, scope: !1778)
!1969 = !DILocation(line: 472, column: 20, scope: !1778)
!1970 = !DILocation(line: 473, column: 31, scope: !1778)
!1971 = !DILocation(line: 473, column: 33, scope: !1778)
!1972 = !DILocation(line: 473, column: 29, scope: !1778)
!1973 = !DILocation(line: 473, column: 11, scope: !1778)
!1974 = !DILocation(line: 473, column: 13, scope: !1778)
!1975 = !DILocation(line: 473, column: 24, scope: !1778)
!1976 = !DILocation(line: 474, column: 9, scope: !1778)
!1977 = !DILocation(line: 477, column: 31, scope: !1978)
!1978 = distinct !DILexicalBlock(scope: !1774, file: !1329, line: 476, column: 9)
!1979 = !DILocation(line: 477, column: 11, scope: !1978)
!1980 = !DILocation(line: 479, column: 7, scope: !1775)
!1981 = !DILocation(line: 482, column: 20, scope: !1982)
!1982 = distinct !DILexicalBlock(scope: !1769, file: !1329, line: 481, column: 7)
!1983 = !DILocation(line: 482, column: 9, scope: !1982)
!1984 = !DILocation(line: 484, column: 5, scope: !1770)
!1985 = !DILocation(line: 487, column: 11, scope: !1986)
!1986 = distinct !DILexicalBlock(scope: !1987, file: !1329, line: 487, column: 11)
!1987 = distinct !DILexicalBlock(scope: !1756, file: !1329, line: 486, column: 5)
!1988 = !DILocation(line: 487, column: 19, scope: !1986)
!1989 = !DILocation(line: 487, column: 27, scope: !1986)
!1990 = !DILocation(line: 487, column: 11, scope: !1987)
!1991 = !DILocation(line: 489, column: 15, scope: !1992)
!1992 = distinct !DILexicalBlock(scope: !1993, file: !1329, line: 489, column: 15)
!1993 = distinct !DILexicalBlock(scope: !1986, file: !1329, line: 488, column: 7)
!1994 = !DILocation(line: 489, column: 17, scope: !1992)
!1995 = !DILocation(line: 489, column: 30, scope: !1992)
!1996 = !DILocation(line: 489, column: 32, scope: !1992)
!1997 = !DILocation(line: 489, column: 38, scope: !1992)
!1998 = !DILocation(line: 489, column: 27, scope: !1992)
!1999 = !DILocation(line: 489, column: 43, scope: !1992)
!2000 = !DILocation(line: 489, column: 46, scope: !1992)
!2001 = !DILocation(line: 489, column: 48, scope: !1992)
!2002 = !DILocation(line: 489, column: 58, scope: !1992)
!2003 = !DILocation(line: 489, column: 60, scope: !1992)
!2004 = !DILocation(line: 489, column: 55, scope: !1992)
!2005 = !DILocation(line: 489, column: 15, scope: !1993)
!2006 = !DILocalVariable(name: "row", scope: !2007, file: !1329, line: 491, type: !47)
!2007 = distinct !DILexicalBlock(scope: !2008, file: !1329, line: 491, column: 15)
!2008 = distinct !DILexicalBlock(scope: !1992, file: !1329, line: 490, column: 11)
!2009 = !DILocation(line: 491, column: 24, scope: !2007)
!2010 = !DILocation(line: 491, column: 20, scope: !2007)
!2011 = !DILocation(line: 491, column: 33, scope: !2012)
!2012 = distinct !DILexicalBlock(scope: !2007, file: !1329, line: 491, column: 15)
!2013 = !DILocation(line: 491, column: 39, scope: !2012)
!2014 = !DILocation(line: 491, column: 37, scope: !2012)
!2015 = !DILocation(line: 491, column: 15, scope: !2007)
!2016 = !DILocation(line: 492, column: 28, scope: !2012)
!2017 = !DILocation(line: 492, column: 36, scope: !2012)
!2018 = !DILocation(line: 492, column: 42, scope: !2012)
!2019 = !DILocation(line: 492, column: 48, scope: !2012)
!2020 = !DILocation(line: 492, column: 50, scope: !2012)
!2021 = !DILocation(line: 492, column: 46, scope: !2012)
!2022 = !DILocation(line: 492, column: 19, scope: !2012)
!2023 = !DILocation(line: 493, column: 24, scope: !2012)
!2024 = !DILocation(line: 493, column: 32, scope: !2012)
!2025 = !DILocation(line: 494, column: 24, scope: !2012)
!2026 = !DILocation(line: 494, column: 38, scope: !2012)
!2027 = !DILocation(line: 494, column: 44, scope: !2012)
!2028 = !DILocation(line: 494, column: 46, scope: !2012)
!2029 = !DILocation(line: 494, column: 42, scope: !2012)
!2030 = !DILocation(line: 494, column: 60, scope: !2012)
!2031 = !DILocation(line: 494, column: 62, scope: !2012)
!2032 = !DILocation(line: 494, column: 58, scope: !2012)
!2033 = !DILocation(line: 494, column: 72, scope: !2012)
!2034 = !DILocation(line: 495, column: 23, scope: !2012)
!2035 = !DILocation(line: 495, column: 25, scope: !2012)
!2036 = !DILocation(line: 494, column: 76, scope: !2012)
!2037 = !DILocation(line: 496, column: 23, scope: !2012)
!2038 = !DILocation(line: 496, column: 33, scope: !2012)
!2039 = !DILocation(line: 491, column: 54, scope: !2012)
!2040 = !DILocation(line: 491, column: 15, scope: !2012)
!2041 = distinct !{!2041, !2015, !2042, !1441}
!2042 = !DILocation(line: 496, column: 57, scope: !2007)
!2043 = !DILocation(line: 497, column: 11, scope: !2008)
!2044 = !DILocation(line: 501, column: 23, scope: !2045)
!2045 = distinct !DILexicalBlock(scope: !1992, file: !1329, line: 499, column: 11)
!2046 = !DILocation(line: 501, column: 31, scope: !2045)
!2047 = !DILocation(line: 501, column: 15, scope: !2045)
!2048 = !DILocation(line: 501, column: 38, scope: !2045)
!2049 = !DILocation(line: 501, column: 46, scope: !2045)
!2050 = !DILocation(line: 501, column: 54, scope: !2045)
!2051 = !DILocation(line: 502, column: 19, scope: !2045)
!2052 = !DILocation(line: 502, column: 21, scope: !2045)
!2053 = !DILocation(line: 502, column: 27, scope: !2045)
!2054 = !DILocation(line: 502, column: 26, scope: !2045)
!2055 = !DILocation(line: 502, column: 38, scope: !2045)
!2056 = !DILocation(line: 504, column: 7, scope: !1993)
!2057 = !DILocation(line: 505, column: 16, scope: !2058)
!2058 = distinct !DILexicalBlock(scope: !1986, file: !1329, line: 505, column: 16)
!2059 = !DILocation(line: 505, column: 24, scope: !2058)
!2060 = !DILocation(line: 505, column: 32, scope: !2058)
!2061 = !DILocation(line: 505, column: 16, scope: !1986)
!2062 = !DILocalVariable(name: "c3image", scope: !2063, file: !1329, line: 507, type: !90)
!2063 = distinct !DILexicalBlock(scope: !2058, file: !1329, line: 506, column: 7)
!2064 = !DILocation(line: 507, column: 26, scope: !2063)
!2065 = !DILocation(line: 507, column: 53, scope: !2063)
!2066 = !DILocation(line: 507, column: 61, scope: !2063)
!2067 = !DILocation(line: 507, column: 69, scope: !2063)
!2068 = !DILocation(line: 507, column: 36, scope: !2063)
!2069 = !DILocalVariable(name: "row", scope: !2070, file: !1329, line: 508, type: !47)
!2070 = distinct !DILexicalBlock(scope: !2063, file: !1329, line: 508, column: 11)
!2071 = !DILocation(line: 508, column: 20, scope: !2070)
!2072 = !DILocation(line: 508, column: 16, scope: !2070)
!2073 = !DILocation(line: 508, column: 29, scope: !2074)
!2074 = distinct !DILexicalBlock(scope: !2070, file: !1329, line: 508, column: 11)
!2075 = !DILocation(line: 508, column: 35, scope: !2074)
!2076 = !DILocation(line: 508, column: 33, scope: !2074)
!2077 = !DILocation(line: 508, column: 11, scope: !2070)
!2078 = !DILocalVariable(name: "srcrow", scope: !2079, file: !1329, line: 510, type: !92)
!2079 = distinct !DILexicalBlock(scope: !2074, file: !1329, line: 509, column: 9)
!2080 = !DILocation(line: 510, column: 19, scope: !2079)
!2081 = !DILocation(line: 511, column: 32, scope: !2079)
!2082 = !DILocation(line: 511, column: 41, scope: !2079)
!2083 = !DILocation(line: 511, column: 47, scope: !2079)
!2084 = !DILocation(line: 511, column: 49, scope: !2079)
!2085 = !DILocation(line: 511, column: 45, scope: !2079)
!2086 = !DILocation(line: 511, column: 63, scope: !2079)
!2087 = !DILocation(line: 511, column: 65, scope: !2079)
!2088 = !DILocation(line: 511, column: 61, scope: !2079)
!2089 = !DILocation(line: 511, column: 15, scope: !2079)
!2090 = !DILocalVariable(name: "dstrow", scope: !2079, file: !1329, line: 512, type: !86)
!2091 = !DILocation(line: 512, column: 19, scope: !2079)
!2092 = !DILocation(line: 512, column: 49, scope: !2079)
!2093 = !DILocation(line: 512, column: 57, scope: !2079)
!2094 = !DILocation(line: 512, column: 63, scope: !2079)
!2095 = !DILocation(line: 512, column: 69, scope: !2079)
!2096 = !DILocation(line: 512, column: 71, scope: !2079)
!2097 = !DILocation(line: 512, column: 67, scope: !2079)
!2098 = !DILocalVariable(name: "col", scope: !2099, file: !1329, line: 513, type: !47)
!2099 = distinct !DILexicalBlock(scope: !2079, file: !1329, line: 513, column: 11)
!2100 = !DILocation(line: 513, column: 20, scope: !2099)
!2101 = !DILocation(line: 513, column: 16, scope: !2099)
!2102 = !DILocation(line: 513, column: 29, scope: !2103)
!2103 = distinct !DILexicalBlock(scope: !2099, file: !1329, line: 513, column: 11)
!2104 = !DILocation(line: 513, column: 35, scope: !2103)
!2105 = !DILocation(line: 513, column: 33, scope: !2103)
!2106 = !DILocation(line: 513, column: 11, scope: !2099)
!2107 = !DILocalVariable(name: "c", scope: !2108, file: !1329, line: 515, type: !47)
!2108 = distinct !DILexicalBlock(scope: !2109, file: !1329, line: 515, column: 13)
!2109 = distinct !DILexicalBlock(scope: !2103, file: !1329, line: 514, column: 11)
!2110 = !DILocation(line: 515, column: 22, scope: !2108)
!2111 = !DILocation(line: 515, column: 18, scope: !2108)
!2112 = !DILocation(line: 515, column: 29, scope: !2113)
!2113 = distinct !DILexicalBlock(scope: !2108, file: !1329, line: 515, column: 13)
!2114 = !DILocation(line: 515, column: 31, scope: !2113)
!2115 = !DILocation(line: 515, column: 13, scope: !2108)
!2116 = !DILocation(line: 516, column: 32, scope: !2113)
!2117 = !DILocation(line: 516, column: 39, scope: !2113)
!2118 = !DILocation(line: 516, column: 41, scope: !2113)
!2119 = !DILocation(line: 516, column: 55, scope: !2113)
!2120 = !DILocation(line: 516, column: 53, scope: !2113)
!2121 = !DILocation(line: 516, column: 60, scope: !2113)
!2122 = !DILocation(line: 516, column: 15, scope: !2113)
!2123 = !DILocation(line: 516, column: 22, scope: !2113)
!2124 = !DILocation(line: 516, column: 27, scope: !2113)
!2125 = !DILocation(line: 516, column: 30, scope: !2113)
!2126 = !DILocation(line: 515, column: 37, scope: !2113)
!2127 = !DILocation(line: 515, column: 13, scope: !2113)
!2128 = distinct !{!2128, !2115, !2129, !1441}
!2129 = !DILocation(line: 516, column: 61, scope: !2108)
!2130 = !DILocation(line: 517, column: 13, scope: !2109)
!2131 = !DILocation(line: 517, column: 20, scope: !2109)
!2132 = !DILocation(line: 517, column: 28, scope: !2109)
!2133 = !DILocation(line: 518, column: 11, scope: !2109)
!2134 = !DILocation(line: 513, column: 49, scope: !2103)
!2135 = !DILocation(line: 513, column: 11, scope: !2103)
!2136 = distinct !{!2136, !2106, !2137, !1441}
!2137 = !DILocation(line: 518, column: 11, scope: !2099)
!2138 = !DILocation(line: 519, column: 9, scope: !2079)
!2139 = !DILocation(line: 508, column: 50, scope: !2074)
!2140 = !DILocation(line: 508, column: 11, scope: !2074)
!2141 = distinct !{!2141, !2077, !2142, !1441}
!2142 = !DILocation(line: 519, column: 9, scope: !2070)
!2143 = !DILocation(line: 520, column: 7, scope: !2063)
!2144 = !DILocation(line: 524, column: 9, scope: !2145)
!2145 = distinct !DILexicalBlock(scope: !2058, file: !1329, line: 522, column: 7)
!2146 = !DILocation(line: 529, column: 9, scope: !2147)
!2147 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 529, column: 9)
!2148 = !DILocation(line: 529, column: 9, scope: !1348)
!2149 = !DILocation(line: 531, column: 7, scope: !2150)
!2150 = distinct !DILexicalBlock(scope: !2147, file: !1329, line: 530, column: 5)
!2151 = !DILocation(line: 532, column: 5, scope: !2150)
!2152 = !DILocation(line: 533, column: 9, scope: !2153)
!2153 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 533, column: 9)
!2154 = !DILocation(line: 533, column: 18, scope: !2153)
!2155 = !DILocation(line: 533, column: 49, scope: !2153)
!2156 = !DILocation(line: 533, column: 52, scope: !2153)
!2157 = !DILocation(line: 533, column: 54, scope: !2153)
!2158 = !DILocation(line: 533, column: 62, scope: !2153)
!2159 = !DILocation(line: 533, column: 64, scope: !2153)
!2160 = !DILocation(line: 533, column: 60, scope: !2153)
!2161 = !DILocation(line: 533, column: 9, scope: !1348)
!2162 = !DILocation(line: 535, column: 7, scope: !2163)
!2163 = distinct !DILexicalBlock(scope: !2153, file: !1329, line: 534, column: 5)
!2164 = !DILocation(line: 536, column: 5, scope: !2163)
!2165 = !DILocation(line: 538, column: 9, scope: !2166)
!2166 = distinct !DILexicalBlock(scope: !1348, file: !1329, line: 538, column: 9)
!2167 = !DILocation(line: 538, column: 9, scope: !1348)
!2168 = !DILocation(line: 540, column: 29, scope: !2169)
!2169 = distinct !DILexicalBlock(scope: !2166, file: !1329, line: 539, column: 5)
!2170 = !DILocation(line: 540, column: 7, scope: !2169)
!2171 = !DILocation(line: 540, column: 9, scope: !2169)
!2172 = !DILocation(line: 540, column: 22, scope: !2169)
!2173 = !DILocation(line: 541, column: 20, scope: !2169)
!2174 = !DILocation(line: 541, column: 22, scope: !2169)
!2175 = !DILocation(line: 541, column: 7, scope: !2169)
!2176 = !DILocation(line: 541, column: 9, scope: !2169)
!2177 = !DILocation(line: 541, column: 17, scope: !2169)
!2178 = !DILocation(line: 543, column: 49, scope: !2169)
!2179 = !DILocation(line: 543, column: 51, scope: !2169)
!2180 = !DILocation(line: 543, column: 61, scope: !2169)
!2181 = !DILocation(line: 543, column: 35, scope: !2169)
!2182 = !DILocation(line: 543, column: 37, scope: !2169)
!2183 = !DILocation(line: 543, column: 47, scope: !2169)
!2184 = !DILocation(line: 543, column: 21, scope: !2169)
!2185 = !DILocation(line: 543, column: 23, scope: !2169)
!2186 = !DILocation(line: 543, column: 33, scope: !2169)
!2187 = !DILocation(line: 543, column: 7, scope: !2169)
!2188 = !DILocation(line: 543, column: 9, scope: !2169)
!2189 = !DILocation(line: 543, column: 19, scope: !2169)
!2190 = !DILocation(line: 544, column: 7, scope: !2169)
!2191 = !DILocation(line: 544, column: 9, scope: !2169)
!2192 = !DILocation(line: 544, column: 15, scope: !2169)
!2193 = !DILocation(line: 545, column: 5, scope: !2169)
!2194 = !DILocation(line: 548, column: 5, scope: !1348)
!2195 = !DILocation(line: 548, column: 13, scope: !1348)
!2196 = !DILocation(line: 548, column: 28, scope: !1348)
!2197 = !DILocation(line: 552, column: 5, scope: !1348)
!2198 = !DILocation(line: 556, column: 5, scope: !2199)
!2199 = distinct !DILexicalBlock(scope: !1384, file: !1329, line: 556, column: 5)
!2200 = !DILocation(line: 558, column: 1, scope: !2199)
!2201 = !DILocation(line: 557, column: 3, scope: !1382)
!2202 = !DILocation(line: 558, column: 1, scope: !1328)
