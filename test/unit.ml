open Dates_calc.Dates

let date = Alcotest.testable format_date (fun x y -> compare_dates x y = 0)

let date_from_ymd str =
  let re = Str.regexp {|\([0-9][0-9]\)/\([0-9][0-9]\)/\([0-9][0-9][0-9][0-9]\)|} in
  assert(Str.string_match re str 0);
  let year = int_of_string @@ Str.matched_group 3 str in
  let month = int_of_string @@ Str.matched_group 2 str in
  let day = int_of_string @@ Str.matched_group 1 str in
  make_date ~year:year ~month:month ~day:day

let period_from_ymd str =
  let re = Str.regexp {|\([0-9][0-9]\)d|} in
  assert(Str.string_match re str 0);
  let days = int_of_string @@ Str.matched_group 1 str in
  make_period ~years:0 ~months:0 ~days:days

let test_add_dates_days () =
  Alcotest.(check date) "bla" (date_from_ymd "30/03/2012") (add_dates (date_from_ymd "20/03/2012") (period_from_ymd "10d"))

(* Run it *)
let () =
  let open Alcotest in
  run "unit" [
      "add_dates", [
          test_case "days"     `Quick test_add_dates_days;
        ];
    ]
