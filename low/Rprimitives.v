(** Rprimitives.
 * This file defines primitive and internals pointers.
 * The structure manipulating them (FUNTAB in R) is defined in the module Rfeatures. **)

Require Export Shared.

Inductive primitive_basics :=
  | primitive_if
  | primitive_while
  | primitive_for
  | primitive_repeat
  | primitive_break
  | primitive_next
  | primitive_return
  | primitive_function
  | primitive_set_1 (** <- **)
  | primitive_set_3 (** = **)
  | primitive_set_2 (** <<- **)
  | primitive_begin (** { **)
  | primitive_paren (** ( **)
  | primitive_subset_dflt (** .subset **)
  | primitive_subset2_dflt (** .subset2 **)
  | primitive_subset_1 (** [ **)
  | primitive_subset_2 (** [[ **)
  | primitive_subset_3 (** $ **)
  | primitive_at (** @ **)
  | primitive_subassign (** [<- **)
  | primitive_subassign2 (** [[<- **)
  | primitive_subassign3 (** $<- **)
  | primitive_switch
  | primitive_browser
  | primitive_trace (** .primTrace **)
  | primitive_untrace (** .primUntrace **)
  | primitive_internal (** .Internal **)
  | primitive_primitive (** .Primitive **)
  | primitive_call
  | primitive_quote
  | primitive_substitute
  | primitive_missing
  | primitive_nargs
  | primitive_on_exit (** on.exit **)
  | primitive_forceAndCall
  .

Instance primitive_basics_Comparable : Comparable primitive_basics.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_basics :=
  | internal_stop
  | internal_warning
  | internal_gettext
  | internal_ngettext
  | internal_bindtextdomain
  | internal_addConHands
  | internal_resetConHands
  | internal_signalCOndition
  | internal_dfltStop
  | internal_dfltWarn
  | internal_addRestart
  | internal_getRestart
  | internal_invokeRestart
  | internal_addTryHandlers
  | internal_geterrmessage
  | internal_seterrmessage
  | internal_printDeferredWarnings
  | internal_interruptsSuspended
  | internal_as_function_default
  | internal_debug
  | internal_undebug
  | internal_isdebugged
  | internal_debugonce
  | internal_Recall
  | internal_delayedAssign
  | internal_makeLazy
  | internal_identical
  | internal_C_tryCatchHelper
  .

Instance internal_basics_Comparable : Comparable internal_basics.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_operators :=
  | primitive_add (** + **)
  | primitive_sub (** - **)
  | primitive_mult (** * **)
  | primitive_div (** / **)
  | primitive_exp (** ^ **)
  | primitive_mod (** %% **)
  | primitive_int_div (** %/% **)
  | primitive_matrix_mult (** %*% **)
  | primitive_eq (** == **)
  | primitive_neq (** != **)
  | primitive_lt (** < **)
  | primitive_le (** <= **)
  | primitive_ge (** >= **)
  | primitive_gt (** > **)
  | primitive_and (** & **)
  | primitive_or (** | **)
  | primitive_neg (** ! **)
  | primitive_lazy_and (** && **)
  | primitive_lazy_or (** || **)
  | primitive_inline_ifthenelse (** : **)
  | primitive_sequence (** : **)
  | primitive_as_in_formula (** ~ **)
  | primitive_all
  | primitive_any
  .

Instance primitive_operators_Comparable : Comparable primitive_operators.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_matrices :=
  | primitive_dotselt (** ...elt **)
  | primitive_dotslength (** ...length **)
  | primitive_length
  | primitive_lengthgets (** length<- **)
  | primitive_c
  | primitive_oldClass
  | primitive_oldClassgets (** oldClass<- **)
  | primitive_class
  | primitive_cache_class (** .cache_class **)
  | primitive_set_class (** class<- **)
  | primitive_unclass
  | primitive_names
  | primitive_namesgets (** names<- **)
  | primitive_dimnames
  | primitive_dimnamesgets (** dimnames<- **)
  | primitive_dim
  | primitive_dimgets (** dim<- **)
  | primitive_attributes
  | primitive_attributesgets (** attributes<- **)
  | primitive_attr
  | primitive_attrgets_0 (** attr<- **)
  | primitive_attrgets_1 (** @<- **)
  | primitive_levelsgets (** levels<- **)
  .

Instance primitive_matrices_Comparable : Comparable primitive_matrices.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_matrices :=
  | internal_vector
  | internal_complex
  | internal_matrix
  | internal_array
  | internal_diag
  | internal_backsolve
  | internal_max_col (** max.col **)
  | internal_row
  | internal_col
  | internal_unlist
  | internal_cbind
  | internal_rbind
  | internal_drop
  | internal_all_names (** all.names **)
  | internal_comment
  | internal_commentgets (** comment<- **)
  | internal_get_1 (** gets **)
  | internal_get_2 (** gets0 **)
  | internal_mget
  | internal_exists
  | internal_assign
  | internal_list2env
  | internal_remove
  | internal_duplicated
  | internal_unique
  | internal_anyDuplicated
  | internal_anyNA
  | internal_which
  | internal_which_min (** which.min **)
  | internal_pmin
  | internal_pmax
  | internal_which_max (** which.max **)
  | internal_match
  | internal_pmatch
  | internal_charmatch
  | internal_match_call (** match.call **)
  | internal_crossprod
  | internal_tcrossprod
  | internal_lengths
  | internal_attach
  | internal_detach
  | internal_search
  | internal_setFileTime
  .

Instance internal_matrices_Comparable : Comparable internal_matrices.
  prove_comparable_simple_inductive.
Defined.

(** There are a lot of mathematical functions. We artifically divide them
  to ease the compilation process. **)
Inductive primitive_mathematical_functions_1 :=
  | primitive_round
  | primitive_signif
  | primitive_log
  | primitive_log10
  | primitive_log2
  | primitive_abs
  | primitive_floor
  | primitive_ceiling
  | primitive_sqrt
  | primitive_sign
  | primitive_trunc
  | primitive_exp_function (** exp **)
  | primitive_expm1
  | primitive_log1p
  | primitive_cos
  | primitive_sin
  | primitive_tan
  | primitive_acos
  | primitive_asin
  | primitive_atan
  | primitive_cosh
  | primitive_sinh
  | primitive_tanh
  | primitive_acosh
  | primitive_asinh
  | primitive_atanh
  | primitive_lgamma
  | primitive_gamma
  | primitive_digamma
  | primitive_trigamma
  | primitive_cospi
  | primitive_sinpi
  | primitive_tanpi
  .

Instance primitive_mathematical_functions_1_Comparable : Comparable primitive_mathematical_functions_1.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_mathematical_functions_2 :=
  | primitive_atan2
  | primitive_lbeta
  | primitive_beta
  | primitive_lchoose
  | primitive_choose
  | primitive_dchisq
  | primitive_pchisq
  | primitive_qchisq
  | primitive_dexp
  | primitive_pexp
  | primitive_qexp
  | primitive_dgeom
  | primitive_pgeom
  | primitive_qgeom
  | primitive_dpois
  | primitive_ppois
  | primitive_qpois
  | primitive_dt
  | primitive_pt
  | primitive_qt
  | primitive_dsignrank
  | primitive_psignrank
  | primitive_qsignrank
  | primitive_besselJ
  | primitive_besselY
  | primitive_psigamma
  | primitive_Re
  | primitive_Im
  | primitive_Mod
  | primitive_Arg
  | primitive_Conj
  .

Instance primitive_mathematical_functions_2_Comparable : Comparable primitive_mathematical_functions_2.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_mathematical_functions_3 :=
  | primitive_dbeta
  | primitive_pbeta
  | primitive_qbeta
  | primitive_dbinom
  | primitive_pbinom
  | primitive_qbinom
  | primitive_dcauchy
  | primitive_pcauchy
  | primitive_qcauchy
  | primitive_df
  | primitive_pf
  | primitive_qf
  | primitive_dgamma
  | primitive_pgamma
  | primitive_qgamma
  | primitive_dlnorm
  | primitive_plnorm
  | primitive_qlnorm
  | primitive_dlogis
  | primitive_plogis
  | primitive_qlogis
  | primitive_dnbinom
  | primitive_pnbinom
  | primitive_qnbinom
  | primitive_dnorm
  | primitive_pnorm
  | primitive_qnorm
  | primitive_dunif
  | primitive_punif
  | primitive_qunif
  | primitive_dweibull
  | primitive_pweibull
  | primitive_qweibull
  .
  
Instance primitive_mathematical_functions_3_Comparable : Comparable primitive_mathematical_functions_3.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_mathematical_functions_4 :=
  | primitive_dnchisq
  | primitive_pnchisq
  | primitive_qnchisq
  | primitive_dnt
  | primitive_pnt
  | primitive_qnt
  | primitive_dwilcox
  | primitive_pwilcox
  | primitive_qwilcox
  | primitive_besselI
  | primitive_besselK
  | primitive_dnbinom_mu
  | primitive_pnbinom_mu
  | primitive_qnbinom_mu
  | primitive_dhyper
  | primitive_phyper
  | primitive_qhyper
  | primitive_dnbeta
  | primitive_pnbeta
  | primitive_qnbeta
  | primitive_dnf
  | primitive_pnf
  | primitive_qnf
  | primitive_dtukey
  | primitive_ptukey
  | primitive_qtukey
  | primitive_polyroot
  .

Instance primitive_mathematical_functions_4_Comparable : Comparable primitive_mathematical_functions_4.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_random_numbers :=
  | primitive_rchisq
  | primitive_rexp
  | primitive_rgeom
  | primitive_rpois
  | primitive_rt
  | primitive_rsignrank
  | primitive_rbeta
  | primitive_rbinom
  | primitive_rcauchy
  | primitive_rf
  | primitive_rgamma
  | primitive_rlnorm
  | primitive_rlogis
  | primitive_rnbinom
  | primitive_rnbinom_mu
  | primitive_rnchisq
  | primitive_rnorm
  | primitive_runif
  | primitive_rweibull
  | primitive_rwilcox
  | primitive_rhyper
  | primitive_sample
  | primitive_sample2
  | primitive_RNGkind
  | primitive_set_seed (** set.seed **)
  .

Instance primitive_random_numbers_Comparable : Comparable primitive_random_numbers.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_data_summaries :=
  | primitive_sum
  | primitive_min
  | primitive_max
  | primitive_prod
  | primitive_mean
  | primitive_range
  | primitive_cumsum
  | primitive_cumprod
  | primitive_cummax
  | primitive_cummin
  .

Instance primitive_data_summaries_Comparable : Comparable primitive_data_summaries.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_type_coercions :=
  | primitive_as_character (** as.character **)
  | primitive_as_integer (** as.integer **)
  | primitive_as_double (** as.double **)
  | primitive_as_numeric (** as.numeric **)
  | primitive_as_complex (** as.complex **)
  | primitive_as_logical (** as.logical **)
  | primitive_as_raw (** as.raw **)
  | primitive_as_call (** as.call **)
  | primitive_as_environment (** as.environment **)
  | primitive_storage_mode (** storage.mode<- **)
  | primitive_asCharacterFactor (** asCharacterFactor **)
  | primitive_as_vector (** as.vector **)
  | primitive_paste_0 (** paste **)
  | primitive_paste_1 (** paste0 **)
  | primitive_file_path (** file.path **)
  | primitive_format
  | primitive_format_info (** format.info **)
  | primitive_cat
  | primitive_do_call (** do.call **)
  .

Instance primitive_type_coercions_Comparable : Comparable primitive_type_coercions.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_string_manipulations :=
  | primitive_nchar
  | primitive_nzchar
  | primitive_substr
  | primitive_startsWith
  | primitive_endsWith
  | primitive_substrgets (** substr<- **)
  | primitive_strsplit
  | primitive_abbreviate
  | primitive_make_names (** make.names **)
  | primitive_pcre_config
  | primitive_grep
  | primitive_grepl
  | primitive_grepRaw
  | primitive_string_sub (** sub **)
  | primitive_gsub
  | primitive_regexpr
  | primitive_gregexpr
  | primitive_regexec
  | primitive_agrep
  | primitive_agrepl
  | primitive_adist
  | primitive_aregexec
  | primitive_tolower
  | primitive_toupper
  | primitive_chartr
  | primitive_sprintf
  | primitive_make_unique (** make.unique **)
  | primitive_charToRaw
  | primitive_rawToChar
  | primitive_rawShift
  | primitive_intToBits
  | primitive_rawToBits
  | primitive_packBits
  | primitive_utf8ToInt
  | primitive_intToUtf8
  | primitive_validUTF8
  | primitive_validEnc
  | primitive_encodeString
  | primitive_iconv
  | primitive_strtrim
  | primitive_strtoi
  | primitive_strrep
  .

Instance primitive_string_manipulations_Comparable : Comparable primitive_string_manipulations.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_type_checking :=
  | primitive_is_null (** is.null **)
  | primitive_is_logical (** is.logical **)
  | primitive_is_integer (** is.integer **)
  | primitive_is_double (** is.double **)
  | primitive_is_complex (** is.complex **)
  | primitive_is_character (** is.character **)
  | primitive_is_symbol (** is.symbol **)
  | primitive_is_name (** is.name **)
  | primitive_is_environment (** is.environment **)
  | primitive_is_list (** is.list **)
  | primitive_is_pairlist (** is.pairlist **)
  | primitive_is_expression (** is.expression **)
  | primitive_is_raw (** is.raw **)
  | primitive_is_object (** is.object **)
  | primitive_isS4
  | primitive_is_numeric (** is.numeric **)
  | primitive_is_matrix (** is.matrix **)
  | primitive_is_array (** is.array **)
  | primitive_is_atomic (** is.atomic **)
  | primitive_is_recursive (** is.recursive **)
  | primitive_is_call (** is.call **)
  | primitive_is_language (** is.language **)
  | primitive_is_function (** is.function **)
  | primitive_is_single (** is.single **)
  | primitive_is_na (** is.na **)
  | primitive_is_nan (** is.nan **)
  | primitive_is_finite (** is.finite **)
  | primitive_is_infinite (** is.infinite **)
  | primitive_is_vector (** is.vector **)
  .

Instance primitive_type_checking_Comparable : Comparable primitive_type_checking.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_miscellaneous :=
  | primitive_proc_time (** proc.time **)
  | primitive_gc_time (** gc.time **)
  | primitive_withVisible
  | primitive_expression
  | primitive_interactive
  | primitive_invisible
  | primitive_rep
  | primitive_rep_int (** rep.int **)
  | primitive_rep_len
  | primitive_seq_int (** seq.int **)
  | primitive_seq_len
  | primitive_seq_along
  | primitive_list
  | primitive_xtfrm
  | primitive_enc2native
  | primitive_enc2utf8
  | primitive_emptyenv
  | primitive_baseenv
  | primitive_globalenv
  | primitive_environmentgets (** environment<- **)
  | primitive_pos_to_env (** pos.to.env **)
  | primitive_eapply
  | primitive_lapply
  | primitive_vapply
  | primitive_mapply
  | primitive_dotC (** .C **)
  | primitive_Fortran (** .Fortran **)
  | primitive_External (** .External **)
  | primitive_External2 (** .External2 **)
  | primitive_Call (** .Call **)
  | primitive_External_graphics (** .External.graphics **)
  | primitive_Call_graphics (** .Call.graphics **)
  .

Instance primitive_miscellaneous_Comparable : Comparable primitive_miscellaneous.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_miscellaneous_1 :=
  | internal_Version
  | internal_machine
  | internal_commandArgs
  | internal_internalsID
  | internal_system
  | internal_shell_exec (** shell.exec **)
  | internal_Sys_which (** Sys.which **)
  | internal_mkjunction
  | internal_tzone_name
  | internal_parse
  | internal_save
  | internal_saveToConn
  | internal_load
  | internal_loadFromConn2
  | internal_serializeToConn
  | internal_unserializeFromConn
  | internal_deparse
  | internal_dput
  | internal_dump
  | internal_quit
  | internal_readline
  | internal_print_default (** print.default **)
  | internal_print_function (** print.function **)
  | internal_prmatrix
  | internal_gc
  | internal_gcinfo
  | internal_gctorture
  | internal_gctorture2
  | internal_memory_profile (** memory.profile **)
  .

Instance internal_miscellaneous_1_Comparable : Comparable internal_miscellaneous_1.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_miscellaneous_2 :=
  | internal_split
  | internal_is_loaded (** is.loaded **)
  | internal_recordGraphics
  | internal_dyn_load (** dyn.load **)
  | internal_dyn_unload (** dyn.unload **)
  | internal_ls
  | internal_typeof
  | internal_eval
  | internal_returnValue
  | internal_sys_parent (** sys.parent **)
  | internal_sys_call (** sys.call **)
  | internal_sys_frame (** sys.frame **)
  | internal_sys_nframe (** sys.nframe **)
  | internal_sys_calls (** sys.calls **)
  | internal_sys_frames (** sys.frames **)
  | internal_sys_on_exit (** sys.on.exit **)
  | internal_sys_parents (** sys.parents **)
  | internal_sys_function (** sys.function **)
  | internal_traceback
  | internal_browserText
  | internal_browserCondition
  | internal_browserSetDebug
  | internal_parent_frame (** parent.frame **)
  | internal_sort
  | internal_is_unsorted (** is.unsorted **)
  | internal_psort
  | internal_qsort
  | internal_radixsort
  | internal_order
  | internal_rank
  | internal_scan
  .

Instance internal_miscellaneous_2_Comparable : Comparable internal_miscellaneous_2.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_miscellaneous_3 :=
  | internal_t_default (** t.default **)
  | internal_aperm
  | internal_builtins
  | internal_args
  | internal_formals
  | internal_body
  | internal_bodyCode
  | internal_environment
  | internal_environmentName
  | internal_env2list
  | internal_reg_finalizer (** reg.finalizer **)
  | internal_options
  | internal_getOption
  | internal_sink
  | internal_sink_number (** sink.number **)
  | internal_rapply
  | internal_islistfactor
  | internal_colSums
  | internal_colMeans
  | internal_rowSums
  | internal_rowMeans
  | internal_tracemem
  | internal_retracemem
  | internal_untracemem
  | internal_inspect
  | internal_address
  | internal_refcnt
  | internal_merge
  | internal_capabilities
  | internal_capabilitiesX11
  | internal_new_env (** new.env **)
  | internal_parent_env (** parent.env **)
  | internal_parent_envgets (** parent.env<- **)
  | internal_topenv
  | internal_l10n_info
  | internal_Cstack_info
  .

Instance internal_miscellaneous_3_Comparable : Comparable internal_miscellaneous_3.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_operating_system :=
  | primitive_file_show (** file.show **)
  | primitive_file_create (** file.create **)
  | primitive_file_remove (** file.remove **)
  | primitive_file_rename (** file.rename **)
  | primitive_file_append (** file.append **)
  | primitive_file_symlink (** file.symlink **)
  | primitive_file_link (** file.link **)
  | primitive_file_copy (** file.copy **)
  | primitive_list_files (** list.files **)
  | primitive_list_dirs (** list.dirs **)
  | primitive_file_exists (** file.exists **)
  | primitive_file_choose (** file.choose **)
  | primitive_file_info (** file.info **)
  | primitive_file_access (** file.access **)
  | primitive_dir_exists (** dir.exists **)
  | primitive_dir_create (** dir.create **)
  | primitive_tempfile
  | primitive_tempdir
  | primitive_R_home (** R.home **)
  | primitive_date
  | primitive_Sys_getenv (** Sys.getenv **)
  | primitive_Sys_setenv (** Sys.setenv **)
  | primitive_Sys_unsetenv (** Sys.unsetenv **)
  | primitive_getwd
  | primitive_setwd
  | primitive_basename
  | primitive_dirname
  | primitive_Sys_chmod (** Sys.chmod **)
  | primitive_Sys_umask (** Sys.umask **)
  | primitive_Sys_readlink (** Sys.readlink **)
  | primitive_Sys_info (** Sys.info **)
  | primitive_Sys_sleep (** Sys.sleep **)
  | primitive_Sys_getlocale (** Sys.getlocale **)
  | primitive_Sys_setlocale (** Sys.setlocale **)
  | primitive_Sys_localeconv (** Sys.localeconv **)
  | primitive_path_expand (** path.expand **)
  | primitive_Sys_getpid (** Sys.getpid **)
  | primitive_normalizePath
  | primitive_Sys_glob (** Sys.glob **)
  | primitive_unlink
  .

Instance primitive_operating_system_Comparable : Comparable primitive_operating_system.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_objects :=
  | primitive_inherits
  | primitive_UseMethod
  | primitive_NextMethod
  | primitive_standardGeneric
  .

Instance primitive_objects_Comparable : Comparable primitive_objects.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_time_manipulations :=
  | primitive_Sys_time (** Sys.time **)
  | primitive_as_POSIXct (** as.POSIXct **)
  | primitive_as_POSIXlt (** as.POSIXlt **)
  | primitive_format_POSIXlt (** format.POSIXlt **)
  | primitive_strptime
  | primitive_Date2POSIXlt
  | primitive_POSIXlt2Date
  .

Instance primitive_time_manipulations_Comparable : Comparable primitive_time_manipulations.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_compilations :=
  | primitive_mkCode
  | primitive_bcClose
  | primitive_is_builtin_internal (** is.builtin.internal **)
  | primitive_disassemble
  | primitive_bcVersion
  | primitive_load_from_file (** load.from.file **)
  | primitive_save_to_file (** save.to.file **)
  | primitive_growconst
  | primitive_putconst
  | primitive_getconst
  | primitive_enableJIT
  | primitive_compilePKGS
  .

Instance primitive_compilations_Comparable : Comparable primitive_compilations.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_connections :=
  | primitive_stdin
  | primitive_stdout
  | primitive_stderr
  | primitive_isatty
  | primitive_readLines
  | primitive_writeLines
  | primitive_readBin
  | primitive_writeBin
  | primitive_readChar
  | primitive_writeChar
  | primitive_open
  | primitive_isOpen
  | primitive_isIncomplete
  | primitive_isSeekable
  | primitive_close
  | primitive_flush
  | primitive_file
  | primitive_url
  | primitive_pipe
  | primitive_fifo
  | primitive_gzfile
  | primitive_bzfile
  | primitive_xzfile
  | primitive_unz
  | primitive_seek
  | primitive_truncate
  | primitive_pushBack
  | primitive_clearPushBack
  | primitive_pushBackLength
  | primitive_rawConnection
  | primitive_rawConnectionValue
  | primitive_textConnection
  | primitive_textConnectionValue
  | primitive_socketConnection
  | primitive_sockSelect
  | primitive_getConnection
  | primitive_getAllConnections
  | primitive_summary_connection (** summary.connection **)
  | primitive_gzcon
  | primitive_memCompress
  | primitive_memDecompress
  | primitive_readDCF
  .

Instance primitive_connections_Comparable : Comparable primitive_connections.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_environments :=
  | primitive_lockEnvironment
  | primitive_environmentIsLocked
  | primitive_lockBinding
  | primitive_unlockBinding
  | primitive_bindingIsLocked
  | primitive_makeActiveBinding
  | primitive_bindingIsActive
  | primitive_mkUnbound
  | primitive_isNamespaceEnv
  | primitive_registerNamespace
  | primitive_unregisterNamespace
  | primitive_getRegisteredNamespace
  | primitive_isRegisteredNamespace
  | primitive_getNamespaceRegistry
  | primitive_importIntoEnv
  | primitive_env_profile (** env.profile **)
  .

Instance primitive_environments_Comparable : Comparable primitive_environments.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_options :=
  | primitive_setNumMathThreads
  | primitive_setMaxNumMathThreads
  | primitive_Encoding
  | primitive_setEncoding
  | primitive_setTimeLimit
  | primitive_setSessionTimeLimit
  | primitive_icuSetCollate
  | primitive_icuGetCollate
  | primitive_readRenviron
  | primitive_shortRowNames
  | primitive_copyDFattr
  | primitive_getRegisteredRoutines
  | primitive_getLoadedDLLs
  | primitive_getSymbolInfo
  | primitive_isMethodsDispatchOn
  | primitive_lazyLoadDBfetch
  | primitive_lazyLoadDBflush
  | primitive_getVarsFromFrame
  | primitive_lazyLoadDBinsertValue
  .

Instance primitive_options_Comparable : Comparable primitive_options.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_codes :=
  | primitive_bincode
  | primitive_tabulate
  | primitive_findInterval
  | primitive_pretty
  | primitive_formatC
  | primitive_crc64
  | primitive_bitwiseAnd
  | primitive_bitwiseNot
  | primitive_bitwiseOr
  | primitive_bitwiseXor
  | primitive_bitwiseShiftL
  | primitive_bitwiseShiftR
  | primitive_serialize
  | primitive_serializeb
  | primitive_unserialize
  | primitive_rowsum_matrix
  | primitive_rowsum_df
  | primitive_setS4Object
  | primitive_traceOnOff
  | primitive_debugOnOff
  .

Instance primitive_codes_Comparable : Comparable primitive_codes.
  prove_comparable_simple_inductive.
Defined.

Inductive internal_lapack :=
  | internal_La_qr_cmplx
  | internal_La_rs_1 (** La_rs **)
  | internal_La_rs_cmplx_2 (** La_rs_cmplx **)
  | internal_La_rg
  | internal_La_rg_cmplx
  | internal_La_rs_5 (** La_rs **)
  | internal_La_rs_cmplx_51 (** La_rs_cmplx **)
  | internal_La_dlange
  | internal_La_dgecon
  | internal_La_dtrcon
  | internal_La_zgecon
  | internal_La_ztrcon
  | internal_La_solve_cmplx
  | internal_La_solve
  | internal_La_qr
  | internal_La_chol
  | internal_La_chol2inv
  | internal_qr_coef_real
  | internal_qr_qy_real
  | internal_det_ge_real
  | internal_qr_coef_cmplx
  | internal_qr_qy_cmplx
  | internal_La_svd
  | internal_La_svd_cmplx
  | internal_La_version
  | internal_La_library
  | internal_bcprofcounts
  | internal_bcprofstart
  | internal_bcprofstop
  | internal_eSoftVersion
  | internal_curlVersion
  | internal_curlGetHeaders
  | internal_curlDownload
  .

Instance internal_lapack_Comparable : Comparable internal_lapack.
  prove_comparable_simple_inductive.
Defined.


(** One symbol for each primitive, that is, construct directly accessible in R. **)
Inductive primitive :=
  | primitive_basic : primitive_basics -> primitive
  | primitive_operator : primitive_operators -> primitive
  | primitive_matrix : primitive_matrices -> primitive
  | primitive_mathematical_function_1 : primitive_mathematical_functions_1 -> primitive
  | primitive_mathematical_function_2 : primitive_mathematical_functions_2 -> primitive
  | primitive_mathematical_function_3 : primitive_mathematical_functions_3 -> primitive
  | primitive_mathematical_function_4 : primitive_mathematical_functions_4 -> primitive
  | primitive_random_number : primitive_random_numbers -> primitive
  | primitive_data_summary : primitive_data_summaries -> primitive
  | primitive_string_manipulation : primitive_string_manipulations -> primitive
  | primitive_type_check : primitive_type_checking -> primitive
  | primitive_misc : primitive_miscellaneous -> primitive
  | primitive_os : primitive_operating_system -> primitive
  | primitive_time_manipulation : primitive_time_manipulations -> primitive
  | primitive_compilation : primitive_compilations -> primitive
  | primitive_connection : primitive_connections -> primitive
  | primitive_environment : primitive_environments -> primitive
  | primitive_option : primitive_options -> primitive
  | primitive_code : primitive_codes -> primitive
  .
Coercion primitive_basic : primitive_basics >-> primitive.
Coercion primitive_operator : primitive_operators >-> primitive.
Coercion primitive_matrix : primitive_matrices >-> primitive.
Coercion primitive_mathematical_function_1 : primitive_mathematical_functions_1 >-> primitive.
Coercion primitive_mathematical_function_2 : primitive_mathematical_functions_2 >-> primitive.
Coercion primitive_mathematical_function_3 : primitive_mathematical_functions_3 >-> primitive.
Coercion primitive_mathematical_function_4 : primitive_mathematical_functions_4 >-> primitive.
Coercion primitive_random_number : primitive_random_numbers >-> primitive.
Coercion primitive_data_summary : primitive_data_summaries >-> primitive.
Coercion primitive_string_manipulation : primitive_string_manipulations >-> primitive.
Coercion primitive_type_check : primitive_type_checking >-> primitive.
Coercion primitive_misc : primitive_miscellaneous >-> primitive.
Coercion primitive_os : primitive_operating_system >-> primitive.
Coercion primitive_time_manipulation : primitive_time_manipulations >-> primitive.
Coercion primitive_compilation : primitive_compilations >-> primitive.
Coercion primitive_connection : primitive_connections >-> primitive.
Coercion primitive_environment : primitive_environments >-> primitive.
Coercion primitive_option : primitive_options >-> primitive.
Coercion primitive_code : primitive_codes >-> primitive.

Instance primitive_Comparable : Comparable primitive.
  prove_comparable_simple_inductive.
Defined.

(** One symbol for each internal, that is, built-in functions present
  in the .Internals R object. **)
Inductive internal :=
  | internal_basic : internal_basics -> internal
  | internal_matrix_op : internal_matrices -> internal
  | internal_misc_1 : internal_miscellaneous_1 -> internal
  | internal_misc_2 : internal_miscellaneous_2 -> internal
  | internal_misc_3 : internal_miscellaneous_3 -> internal
  | internal_lapack_function : internal_lapack -> internal
  .
Coercion internal_basic : internal_basics >-> internal.
Coercion internal_matrix_op : internal_matrices >-> internal.
Coercion internal_misc_1 : internal_miscellaneous_1 >-> internal.
Coercion internal_misc_2 : internal_miscellaneous_2 >-> internal.
Coercion internal_misc_3 : internal_miscellaneous_3 >-> internal.
Coercion internal_lapack_function : internal_lapack >-> internal.

Instance internal_Comparable : Comparable internal.
  prove_comparable_simple_inductive.
Defined.

Inductive primitive_construction :=
  | primitive_construction_primitive : primitive -> primitive_construction
  | primitive_construction_internal : internal -> primitive_construction
  .
Coercion primitive_construction_primitive : primitive >-> primitive_construction.
Coercion primitive_construction_internal : internal >-> primitive_construction.

Instance primitive_construction_Comparable : Comparable primitive_construction.
  prove_comparable_simple_inductive.
Defined.

