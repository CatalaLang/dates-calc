open Dates_calc.Dates

let date = Alcotest.testable format_date (fun x y -> compare_dates x y = 0)

let date_from_ymd str =
  let re =
    Str.regexp {|\([0-9][0-9]\)-\([0-9][0-9]\)-\([0-9][0-9][0-9][0-9]\)|}
  in
  assert (Str.string_match re str 0);
  let year = int_of_string @@ Str.matched_group 3 str in
  let month = int_of_string @@ Str.matched_group 2 str in
  let day = int_of_string @@ Str.matched_group 1 str in
  make_date ~year ~month ~day

let period_from_ymd str =
  let re_d = Str.regexp {|\([0-9]?[0-9]\)d|} in
  let re_m = Str.regexp {|\([0-9]?[0-9]\)m|} in
  let re_y = Str.regexp {|\([0-9]?[0-9]\)y|} in
  if Str.string_match re_d str 0 then
    let days = int_of_string @@ Str.matched_group 1 str in
    make_period ~years:0 ~months:0 ~days
  else if Str.string_match re_m str 0 then
    let months = int_of_string @@ Str.matched_group 1 str in
    make_period ~years:0 ~months ~days:0
  else if Str.string_match re_y str 0 then
    let years = int_of_string @@ Str.matched_group 1 str in
    make_period ~years ~months:0 ~days:0
  else assert false

let check_eqs eqs =
  List.iter
    (fun (d1, delta, d2) ->
      (* checks that d1 + delta = d2 under all rounding modes *)
      List.iter
        (fun rmode ->
          Alcotest.(check date)
            (Format.asprintf "%s + %3s = %s" d1 delta d2)
            (date_from_ymd d2)
            (add_dates ~round:rmode (date_from_ymd d1) (period_from_ymd delta)))
        [RoundUp; RoundDown; AbortOnRound])
    eqs

let check_extended_eqs eqs =
  List.iter
    (fun (d1, delta, dru, drd) ->
      (* checks that d1 +up delta = dru, d1+down delta = drd, d1+abort delta
         aborts withou AmbiguousComputation *)
      Alcotest.(check date)
        (Format.asprintf "%s +up %3s = %s" d1 delta dru)
        (date_from_ymd dru)
        (add_dates ~round:RoundUp (date_from_ymd d1) (period_from_ymd delta));
      Alcotest.(check date)
        (Format.asprintf "%s +down %3s = %s" d1 delta drd)
        (date_from_ymd drd)
        (add_dates ~round:RoundDown (date_from_ymd d1) (period_from_ymd delta));
      Alcotest.check_raises (Format.asprintf "%s +abort %3s raises" d1 delta)
        AmbiguousComputation (fun () ->
          let _ =
            add_dates ~round:AbortOnRound (date_from_ymd d1)
              (period_from_ymd delta)
          in
          ()))
    eqs

let test_add_dates_days () =
  let eqs =
    [
      "20-03-2012", "10d", "30-03-2012";
      "31-03-2012", "1d", "01-04-2012";
      "28-02-2012", "1d", "29-02-2012";
      "28-02-2013", "1d", "01-03-2013";
      "01-03-2012", "71d", "11-05-2012";
      "01-11-2012", "71d", "11-01-2013";
    ]
  in
  check_eqs eqs

let test_add_dates_months_exact () =
  let eqs =
    [
      "15-02-2012", "2m", "15-04-2012";
      "28-02-2012", "4m", "28-06-2012";
      "15-03-2012", "1m", "15-04-2012";
      "15-11-2012", "3m", "15-02-2013";
      "31-03-2012", "2m", "31-05-2012";
      "31-01-2012", "2m", "31-03-2012";
      "31-01-2013", "2m", "31-03-2013";
      "31-10-2012", "5m", "31-03-2013";
    ]
  in
  check_eqs eqs

let test_add_dates_months_ambiguous () =
  let eqs =
    [
      "31-03-2012", "1m", "01-05-2012", "30-04-2012";
      "31-03-2012", "3m", "01-07-2012", "30-06-2012";
      "31-01-2012", "1m", "01-03-2012", "29-02-2012";
      "31-01-2012", "3m", "01-05-2012", "30-04-2012";
      "31-01-2013", "1m", "01-03-2013", "28-02-2013";
      "31-01-2013", "3m", "01-05-2013", "30-04-2013";
      "31-10-2012", "4m", "01-03-2013", "28-02-2013";
      "31-10-2012", "6m", "01-05-2013", "30-04-2013";
      "29-10-2012", "4m", "01-03-2013", "28-02-2013";
    ]
  in
  check_extended_eqs eqs

let test_add_dates_years_exact () =
  let eqs =
    [
      "01-01-2012", "1y", "01-01-2013";
      "28-02-2012", "4y", "28-02-2016";
      "29-02-2012", "4y", "29-02-2016";
      "15-03-2012", "1y", "15-03-2013";
      "15-11-2012", "3y", "15-11-2015";
    ]
  in
  check_eqs eqs

let test_add_dates_years_ambiguous () =
  let eqs =
    [
      "29-02-2012", "1y", "01-03-2013", "28-02-2013";
      "29-02-2012", "88y", "01-03-2100", "28-02-2100";
    ]
  in
  check_extended_eqs eqs

(* Run it *)
let () =
  let open Alcotest in
  run "unit"
    [
      ( "add_dates",
        [
          test_case "days" `Quick test_add_dates_days;
          test_case "months_exact" `Quick test_add_dates_months_exact;
          test_case "months_ambig" `Quick test_add_dates_months_ambiguous;
          test_case "years_exact" `Quick test_add_dates_years_exact;
          test_case "years_ambig" `Quick test_add_dates_years_ambiguous;
        ] );
    ]
