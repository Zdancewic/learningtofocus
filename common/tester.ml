open Arg
open Unix

let prover = ref "/Users/stevez/tp/_build/main.native -backtrack"
let problems_path = ref "/Users/stevez/tp/ILTP-v1.1.2-propositional/Problems/"
let dirs = ref []
let files = ref []
let time_limit = ref 20
let excluded_files = ref [Str.regexp_string "."] 

let add_exclude x =
	let l = !excluded_files in
	excluded_files := (Str.regexp_string x)::l
	
let excluded fn =
	List.exists (fun x -> Str.string_match x fn 0) (!excluded_files)

let argspec = [
	("-prover", String (fun x -> prover := x), "set the prover executable default: main");
	("-path", String (fun x -> problems_path := x), "set the path to the Problems directory");
	("-ex", String (fun x -> add_exclude x), "exclude test files with the given prefix"); 
	("-limit", Arg.Set_int time_limit, "set the time limit in seconds; default = " ^ (string_of_int !time_limit));
	("-dir", String (fun x -> 
			let ds = !dirs in 
				dirs := x::ds), "process an entire subdirectory of Problems")
]

let add_file x = 
		let s = !files in
		files := (x::s)
		
let test_file ?(dn = ".") fn =
	let cmd = Printf.sprintf "time timeout %s %s %s/%s" (string_of_int !time_limit) (!prover) dn fn in
	let _ = Printf.printf "\n-------------------------\n" in
	let _ = Printf.printf "Running: %s" cmd; print_newline () in
	let stat = system cmd in
	 match stat with
	  | (WEXITED i | WSIGNALED i | WSTOPPED i) -> 
				if i = 124 then 
				  (Printf.printf "TIMEOUT\n";
					add_exclude (String.sub fn 0 6)) 
				else Printf.printf "\n"

let test_dir dn =
	let _ = Printf.printf "Directory: %s\n" dn in
	let dhandle = opendir dn in
	try
		while true do
			let fn = readdir dhandle in
			if not (excluded fn) then
			  test_file ~dn:dn fn
			else 
				Printf.printf "Skipped: %s\n" fn
	  done
  with End_of_file -> closedir dhandle
	

let _ = 
	Arg.parse argspec add_file "test a theorem prover";;

Printf.printf "Testing %s\n----------\n" !prover;
List.iter test_file !files;
List.iter test_dir (List.map (fun x -> (!problems_path) ^ x) (!dirs))

