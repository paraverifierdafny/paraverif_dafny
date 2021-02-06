open Core.Std
open Utils
open Paramecium
open Loach

open InvFinder

open Isa_base




let spaces = ref 2

let gen_spaces () = String.make (!spaces) ' ' 
let paraNameMapSymbolName_table= Hashtbl.create ~hashable:String.hashable ()
(*tname->N e.g., Node -> N0, DATA ->N1
when deal with v:array [NODE] of vt; we need record v->N0, which helps to generate v.length =N *)
let var2SymbNoTab= Hashtbl.create ~hashable:String.hashable ()
let record_table = Hashtbl.create ~hashable:String.hashable ()
(**vartable is stored the complex vardef like key :Cache_Data data:array<DATA>*)
let vartable = Hashtbl.create ~hashable:String.hashable ()
let onetable = Hashtbl.create ~hashable:String.hashable ()
let secondtable = Hashtbl.create ~hashable:String.hashable ()
let symbOrder=ref 0
let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false   
(**generate the transformation from const type to string,and int const stored in the paraNameMapSymbolName_table*)
let const_act c =
  match c with
  | Intc(i) -> Int.to_string i
  | Strc(s) -> s
  | Boolc(b) -> Bool.to_string b
let type_act t = 
  let Enum(name, consts) = t in
  match consts with
  | c::_ ->
    begin
      match c with
      | Boolc(_) -> ""
      | Strc(_) ->
        let items_str = String.concat ~sep:"| " (List.map consts ~f:const_act) in
        sprintf "datatype %s = %s"  name items_str
      | Intc(_) ->
        begin
        Hashtbl.replace paraNameMapSymbolName_table ~key:name ~data:!symbOrder;
        symbOrder:=!symbOrder+1;
        sprintf "type %s=nat" name
        end
    end
  | _ -> raise Empty_exception

type node =
  | Node of string * paramdef list * node list * string

let find_vdp vd_part ls =
  let (name, pds) = vd_part in
  let rec wrapper heads ls =
    match ls with
    | [] -> Node(name, pds, [], ""), heads
    | i::ls' ->
      let Node(name', _, _, _) = i in
      if name = name' then
        i, (heads@ls')
      else begin
        wrapper (heads@[i]) ls'
      end
  in
  wrapper [] ls
(**transform arrdefs to node list*)
let build_vars_tree vardefs =
  let rec traverse cur_list ~cur_vd ~tname =
    match cur_vd with
    | [] -> cur_list
    | vd_part::cur_vd' ->
      let (Node(name, pds, next_ls, _)), cur_list = find_vdp vd_part cur_list in
      let next_ls = traverse next_ls ~cur_vd:cur_vd' ~tname in
      if cur_vd' = [] then
        (Node(name, pds, next_ls, tname))::cur_list
      else begin
        (Node(name, pds, next_ls, ""))::cur_list
      end
  in
  List.fold vardefs ~init:[] ~f:(fun res x ->
    let Arrdef(vd_parts, tname) = x in
    traverse res ~cur_vd:vd_parts ~tname
  )

(**get the nodes'name*)
let get_type_id nodes =
  let names = List.map nodes ~f:(fun (Node(name, _, _, _)) -> name)  in 
  String.concat ~sep:","  names 

(**get the nodes'type name*) 
let get_type_name nodes =
  let names = List.map nodes ~f:(fun (Node(_, _, _, tname)) -> tname) in
  String.concat ~sep:","  names 
(**print the string option*)
let print_option option = match option with 
  |Some(m)->sprintf "%s" m
  |None ->sprintf " "

let gen_var_str trees =
  let records = ref [] in
  let get_arr_of pds base_t varName=
    List.fold pds ~init:base_t
     ~f:(fun res a -> match a with 
    			(Paramdef(n, t)) ->
    			if (Hashtbl.mem   paraNameMapSymbolName_table t) 
    			then begin
    				let result=Hashtbl.find paraNameMapSymbolName_table t in
          	(match result with
          	|Some(symbN)->	Hashtbl.replace var2SymbNoTab ~key:varName ~data:symbN
          	|None -> ()); sprintf "array<%s>" res 
          	end
    			else begin Hashtbl.replace paraNameMapSymbolName_table ~key:t ~data:!symbOrder;
    				 	symbOrder:=!symbOrder+1;  
    				  sprintf "array<%s>" res end )
  in
  let rec wrapper tree =
    match tree with
    | Node(name, pds, [], tname) -> let t = Hashtbl.replace vartable ~key: name ~data:(if List.is_empty pds then (sprintf "array<%s>" (get_arr_of pds tname name)) else (get_arr_of pds tname name)) in sprintf "%s: array<%s>" name (get_arr_of pds tname name);
    | Node(name, pds, nodes, tname) ->
      begin
        let key1 = get_type_id nodes in
        let key2 = get_type_name nodes in 
        match Hashtbl.find record_table key1 with
        | Some(record_name) ->
        	let result=Hashtbl.find paraNameMapSymbolName_table record_name in
          	(match result with
          	|Some(symbN)->	Hashtbl.replace var2SymbNoTab ~key:name ~data:symbN
            |None -> ()); 
          let temp=List.map ~f:(fun x -> Hashtbl.replace onetable ~key:(name) ~data:(name^"_"^x)) (String.split ~on:',' (key1)) in
          let t=List.map2_exn ~f:(fun x y -> Hashtbl.replace secondtable ~key:(name^"_"^x) ~data:(if List.is_empty pds then (sprintf "array<%s>" (get_arr_of pds y name)) else (get_arr_of pds y name))) (String.split ~on:',' (key1))  (String.split ~on:',' (key2)) in
          let t1 =  (List.map2_exn ~f:(fun x y ->(List.map ~f:(fun t-> if contains t x then Hashtbl.replace vartable ~key:(name^"_"^t) ~data:(Hashtbl.find_exn secondtable t) else Hashtbl.replace vartable ~key:(name^"_"^x) ~data:(get_arr_of pds y name))) (Hashtbl.keys secondtable)) (String.split ~on:',' (key1))  (String.split ~on:',' (key2))) in 
          String.concat ~sep:",\n" (
          List.map2_exn ~f:(fun x y -> sprintf "%s:%s" (String.concat ~sep:"" (List.map ~f:(fun t-> if contains t x then sprintf "%s" t else "") (Hashtbl.keys secondtable)))
          (if Hashtbl.mem onetable x then Hashtbl.find_exn secondtable (Hashtbl.find_exn onetable x) else get_arr_of pds y name)) 
          (String.split ~on:',' (key1))  (String.split ~on:',' (key2))
          );
        | None ->
          let sub_items = List.map nodes ~f:wrapper in
          let record_name = sprintf "class_%d " (Hashtbl.length record_table) in
          let record_body =  (String.concat ~sep:",\n" sub_items)in
          let record_str = sprintf "class  %s {\nvar \n%s\n}" record_name record_body in
          records := (!records)@[record_str];
          Hashtbl.replace record_table ~key:key1 ~data:record_name;
          let result=Hashtbl.find paraNameMapSymbolName_table record_name in
          	(match result with
          	|Some(symbN)->	Hashtbl.replace var2SymbNoTab ~key:name ~data:symbN
            |None -> ()); 
          let temp=List.map ~f:(fun x -> Hashtbl.replace onetable ~key:(name) ~data:(name^"_"^x)) (String.split ~on:',' (key1)) in
          let t=List.map2_exn ~f:(fun x y -> Hashtbl.replace secondtable ~key:(name^"_"^x) ~data:(if List.is_empty pds then (sprintf "array<%s>" (get_arr_of pds y name)) else (get_arr_of pds y name))) (String.split ~on:',' (key1))  (String.split ~on:',' (key2)) in
          let t1 =  (List.map2_exn ~f:(fun x y ->(List.map ~f:(fun t-> if contains t x then Hashtbl.replace vartable ~key:(name^"_"^t) ~data:(Hashtbl.find_exn secondtable t) else Hashtbl.replace vartable ~key:(name^"_"^x) ~data:((get_arr_of pds y name)))) (Hashtbl.keys secondtable)) (String.split ~on:',' (key1))  (String.split ~on:',' (key2))) in 
          String.concat ~sep:",\n" (
          List.map2_exn ~f:(fun x y -> sprintf "%s:%s" (String.concat ~sep:"" (List.map ~f:(fun t-> if contains t x then sprintf "%s1234" t else "") (Hashtbl.keys secondtable)))
          (if Hashtbl.mem onetable x then Hashtbl.find_exn secondtable (Hashtbl.find_exn onetable x) else get_arr_of pds y name)
          ) 
          (String.split ~on:',' (key1))  (String.split ~on:',' (key2))
          ) ;
        end
  in
  let vars = List.map trees ~f:wrapper in
  (!records), vars

let record_act vardefs =
  let trees = build_vars_tree vardefs in
  let record_defs, var_defs = gen_var_str trees in
  sprintf "\n\n"

(**transform paramref to string*)
let paramref_act pr =
  match pr with
  | Paramfix(_, _, c) -> const_act c
  | Paramref(name) -> name
(**transform arr list to string*)
let var_act v =
  let Arr(ls) = v in
  let str=String.concat ~sep:"_" (List.map ls ~f:(fun (n, prs) -> sprintf "%s" n )) in 
  let str1 =String.concat ~sep:"" (List.map ls ~f:(fun (n, prs) -> 
  match prs with 
  | [] -> sprintf ""
  |  _ ->
    let actual_ps = List.map prs ~f:paramref_act in
    sprintf "%s" (String.concat (List.map actual_ps ~f:(fun p -> sprintf "[%s]" p)))
  )) in 
  let temp = sprintf "%s%s" str str1 in 
  if String.contains temp '[' then sprintf "%s" temp else sprintf "%s[0]" temp
  
  

let paramdef_act'' (Paramdef(vn, tn)) = 
	let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
	sprintf "%s  |0<= %s<N%d" vn vn	symbOrd  
let paramdef_act''' (Paramdef(vn, tn)) = 
	sprintf "%s" vn  
let rec exp_act exp =
  match exp with
  | Const(c) -> const_act c
  | Var(v) -> var_act v
  | Param(pr) -> paramref_act pr
  | Ite(f, e1, e2) ->
    sprintf "if (%s) then %s else %s)" (form_act f) (exp_act e1) (exp_act e2)
  | UIF(n, el) -> sprintf "(%s)" (String.concat ~sep:n (List.map el ~f:exp_act))
and form_act form =
  match form with
  | Chaos -> "true"
  | Miracle -> "false"
  | UIP(n, el) -> sprintf "(%s)" (String.concat ~sep:n (List.map el ~f:exp_act))
  | Eqn(e1, e2) -> sprintf "(%s == %s)" (exp_act e1) (exp_act e2)
  | Neg(form) -> sprintf "(!%s)" (form_act form)
  | AndList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"true" ~f:(fun res x -> sprintf "%s && %s" res x)
    |> sprintf "(%s)"
  | OrList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"false" ~f:(fun res x -> sprintf "%s || %s" res x)
    |> sprintf "(%s)"
  | Imply(f1, f2) -> sprintf "(%s ==> %s)" (form_act f1) (form_act f2)
  | ForallFormula(pds, f) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act'') in
    sprintf "(forall %s :: %s )" pds_str (form_act f)
  | ExistFormula(pds, f) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act'') in
    sprintf "(exists %s :: %s)" pds_str (form_act f)


	
let rec statement_act s =
  match s with
  | Assign(v, e) -> sprintf "%s%s := %s;" (gen_spaces ()) (var_act v) (exp_act e)
  | Parallel(ss) -> String.concat ~sep:"\n" (List.map ss ~f:statement_act)
  | IfStatement(f, s) ->
    spaces := (!spaces) + 2;
    let s_str = statement_act s in
    spaces := (!spaces) - 2;
    sprintf "%sif %s {\n%s\n%s}" (gen_spaces ()) (form_act f) s_str (gen_spaces ())
  | IfelseStatement(f, s1, s2) ->
    spaces := (!spaces) + 2;
    let s1_str = statement_act s1 in
    let s2_str = statement_act s2 in
    spaces := (!spaces) - 2;
    sprintf "%sif %s {\n%s}\nelse{\n%s\n%s}" (gen_spaces ()) (form_act f) s1_str s2_str (gen_spaces ())
  | ForStatement(s, pds) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act''') in
    spaces := (!spaces) + 2;
    let s_str = statement_act s in
    spaces := (!spaces) - 2;
    (* sprintf "%sforall %s {\n%s\n%s}" (gen_spaces ()) pds_str s_str (gen_spaces ()) *)
    sprintf "%svar %s:=0;\n%swhile(%s<N0)\n%s%sdecreases N0-%s\n {\n%s\n%s\n %s:=%s+1;\n}" (gen_spaces ()) pds_str (gen_spaces ()) pds_str (gen_spaces ()) (gen_spaces ())  pds_str s_str (gen_spaces ()) pds_str pds_str

 

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false    
(*contains "abcde" "bc";;*)
let elimia str=
			let ()=print_endline ("elimi "^str) in
			match  String.index str '['     with
			|Some(j)->String.sub ~pos:0 ~len:(j  ) str
			|None -> str  

let getallArrNames str=
	let splitStrs = String.split_on_chars ~on:['_'] str in
	let construc i=
		match  String.find ~f:(fun x-> x='[') 
			(match List.nth splitStrs i with |Some(one) ->one ) with
		 	|Some(j)->[String.concat ~sep:"_" (List.filter ~f:(fun x-> not (x="")) 
		 																			(List.mapi ~f:(fun k a -> 
		 																			   if k<=i then begin if k=(List.length splitStrs - 1) then (elimia a) else a end  else "" ) splitStrs))
		 							 ]
		 	|None ->[] in
    List.concat (List.map ~f:construc (up_to (List.length 	splitStrs)))

let getallInvnames str = String.split_on_chars ~on:['[';']'] str

let rule_act  types  nameAdd extraInvParas reqStr ensureStr varNamesOfInv  r=
  let Rule(name, pds, f, s) = r in
  let varNamesOfStatements =
  	(let ()=VarNamesWithParam.of_var_ref :=  (fun _x -> String.Set.of_list [var_act _x]) in
  	 VarNamesWithParam.of_statement s ~types)   in
  let varNameOfGuards= 
  	(let ()=VarNamesWithParam.of_var_ref :=  (fun _x -> String.Set.of_list [var_act _x]) in
     VarNamesWithParam.of_form f ~types)   in 	 
  let varNamesOfStatementsLeft =(let ()=VarNamesWithParam.of_var_ref :=  (fun _x -> String.Set.of_list [var_act _x]) in
  	 VarNamesWithParam.of_statement_left s ~types)   in
  let varInEnsures=String.Set.union_list [varNamesOfStatementsLeft;varNamesOfInv;varNameOfGuards] in	
  let varNames=String.Set.union_list [varNamesOfStatements;varNameOfGuards;varNamesOfStatementsLeft;varNamesOfInv] in	

  let allArrNames=remove_duplicates (List.concat (List.map ~f:getallInvnames ( (Set.to_list varNames)))) in
  let allModiArrNames=remove_duplicates (List.concat (List.map ~f:getallArrNames ( (Set.to_list varNamesOfStatements)))) in
  let allModifyConstr=String.concat ~sep:"\n" 
  	(List.map ~f:(fun x->sprintf "modifies %s" x) allModiArrNames) in
  let allNames=Hashtbl.keys var2SymbNoTab in 
  let allRequiresNames=remove_duplicates (List.concat (List.map ~f:getallInvnames ( (Set.to_list varInEnsures)))) in

  let containArrName n=
    	List.find    allNames  (fun x->contains n x) in
  let	varNamesOfInv_str=String.concat ~sep:"," (String.Set.to_list varInEnsures) in
  let varInEnsures_str=String.concat ~sep:"," (String.Set.to_list varInEnsures) in
  if pds = [] then
    let guard = sprintf "//guard condition\nrequires %s%s" (gen_spaces ()) (form_act f) in
    let statements = statement_act s in
    let paramdefInRule_act pdf=
   			let (Paramdef(vn, tn)) = pdf in
				let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
				(sprintf "requires 0<=%s<N%d\n" vn 	symbOrd 
         )  in
    let paramdef2Nat pdf=
          let (Paramdef(vn, tn)) = pdf in
         let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
         (sprintf "%s:nat" vn 
          )  in
    let param_str = 
      String.concat ~sep:"" (List.map ~f:paramdefInRule_act pds) in
    let param_str1 = 
        String.concat ~sep:"," (List.map ~f:paramdef2Nat pds) in
    let pds_str = 
      String.concat ~sep:" " 
      (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "%s:%s," x (Hashtbl.find_exn vartable x)) else (sprintf "")) allRequiresNames)   in
    let param_constr_str2 = String.concat ~sep:"\n" 
    (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "requires %s.Length==N0" (x)) else (sprintf ""))  allRequiresNames) in 
    let new_constr = String.concat ~sep:"\n" 
    (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "requires forall i,j::0<=i<%s.Length&&0<=j<%s.Length==>%s[i]!=%s[j]" x x x x) else (sprintf ""))  allRequiresNames) in 
    let paramStr="()" in
    sprintf "\nmethod %s%s\n%s\n%s\n%s\n{\n%s\n}"  (name^nameAdd) 
    (sprintf "(%s\n%s\n%s)" pds_str ("N0:nat,") (if (extraInvParas="") then ("p__Inv0:nat,p__Inv2:nat") else (extraInvParas)) )
    ("requires N0>0\n"^param_constr_str2^"\n"^new_constr^"\n"^(if (extraInvParas="") then ("") else (reqStr))^guard) 
    (ensureStr) allModifyConstr statements



  else begin
    let guard = sprintf "requires %s //guard condition" (form_act f) in
    let statements = statement_act s in
    let sp="" in
    let paramdefInRule_act pdf=
   			let (Paramdef(vn, tn)) = pdf in
				let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
				(sprintf "requires 0<=%s<N%d\n" vn 	symbOrd 
         )  in
    let paramdef2Nat pdf=
      let (Paramdef(vn, tn)) = pdf in
      let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
      (sprintf "%s:nat,N%d:nat" vn symbOrd)  in
    let paramdef2Nat1 pdf=
      let (Paramdef(vn, tn)) = pdf in
      let Some(symbOrd)=Hashtbl.find paraNameMapSymbolName_table tn in
    (sprintf "requires N%d>0\n" symbOrd)  in
    let param_str = 
      String.concat ~sep:"" (List.map ~f:paramdefInRule_act pds) in
    let param_str1 = 
        "N0:nat,"^(String.concat ~sep:"," (List.map ~f:paramdef2Nat pds)) in
    let requires_str = 
        String.concat ~sep:"" (List.map ~f:paramdef2Nat1 pds) in
    let pds_str = 
      String.concat ~sep:" " 
      (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "%s:%s," x (Hashtbl.find_exn vartable x)) else (sprintf "")) allRequiresNames)   in
    let param_constr_str2 = String.concat ~sep:"\n" 
    (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "requires %s.Length==N0" (x)) else (sprintf ""))  allRequiresNames) in 
    let new_constr = String.concat ~sep:"\n" 
    (List.map ~f:(fun x-> if (Hashtbl.mem vartable x) then (sprintf "requires forall i,j::0<=i<%s.Length&&0<=j<%s.Length==>%s[i]!=%s[j]" x x x x) else (sprintf ""))  allRequiresNames) in 
    let rstr =
      sprintf "%smethod %s%s%s%s\n%s\n%s\n{\n%s\n%s}\n"    
      sp
      (name^nameAdd)
      (sprintf "(%s\n%s,\n%s)" pds_str (String.concat ~sep:"," (remove_duplicates(String.split ~on:',' param_str1))) (if (extraInvParas="") then ("p__Inv0:nat,p__Inv2:nat") else (extraInvParas)) )
      (sprintf "\n%s\n%s\n%s\n%s%s\n%s\n" requires_str param_constr_str2 new_constr param_str (if (extraInvParas="") then ("") else (reqStr)) guard)
      (ensureStr)  
      allModifyConstr 
       sp statements sp in
       rstr
  end   