open Dates_calc.Dates

let rec date_generator gen =
  let open QCheck.Gen in
  map3 (fun y m d ->
      try make_date ~year:y ~month:m ~day:d
      with InvalidDate ->
        (* let () = Format.printf "%02d-%02d-%04d invalid, sampling again@." d m y in *)
        date_generator gen)
    (int_range 0 10000) (int_range 1 12) (int_range 1 31) gen

let date =
  QCheck.make ~print:(Format.asprintf "%a" format_date) date_generator

let add_dates_days_check (d, x) =
  (* - forall d, forall x, compare_dates (add_dates_days (add_dates_days d x) -x ) d = 0 *)
  let x_days = make_period ~years:0 ~months:0 ~days:x in
  compare_dates (add_dates (add_dates d x_days) (neg_period x_days)) d = 0

let add_sub_dates_days_check (d1, d2) =
  (* - forall d1 d2, compare_dates (add_dates d2 (sub_dates d1 d2)) d1 = 0 *)
  compare_dates (add_dates d2 (sub_dates d1 d2)) d1 = 0

let t1 = QCheck.Test.make ~count:1000 (QCheck.pair date (QCheck.int_range 0 365000)) add_dates_days_check

let t2 = QCheck.Test.make ~count:1000 (QCheck.pair date date) add_sub_dates_days_check


let () =
  exit @@ QCheck_base_runner.run_tests ~verbose:true [t1; t2]
