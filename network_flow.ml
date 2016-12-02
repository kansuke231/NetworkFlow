
module Graph = struct

  let init_graph () = Hashtbl.create 1000 (* change this value according to the size of the network *)

  let add_edges edge_list g = List.iter (fun (s,d) -> Hashtbl.add g s d) edge_list
  let add_edge edge g = let (i,j) = edge in Hashtbl.add g i j

  let remove_edge_tree edge g_tree =
    let (i,j) = edge in
    let all_nodes = Hashtbl.find_all g_tree i in
    List.iter
      (fun node -> Hashtbl.remove g_tree i) all_nodes; (* First remove everything *)
    List.iter
      (fun node -> if node <> j then Hashtbl.add g_tree i node) all_nodes (* Then put them back except the node j *)

  let get_edgelist g = Hashtbl.fold (fun s t l -> (s,t) :: l) g []
  let get_adjacent_nodes g v = Hashtbl.find_all g v

  let get_nodes g =
    let rec crunch_edges edge_list acc =
      match edge_list with
      | [] -> acc
      | (s,d)::t ->
        let new_acc = [s] @ [d] @ acc in
        crunch_edges t new_acc
    in
    let edge_list = get_edgelist g in
    let nodes = List.sort_uniq compare (crunch_edges edge_list []) in
    nodes

  let get_non_tree_edges g g_tree =
    let g_edges = get_edgelist g in
    let g_tree_edges = get_edgelist g_tree in
    List.filter (fun edge -> not (List.mem edge g_tree_edges) ) g_edges

  let check_edge g edge =
    let (i,j) = edge in
    let edges = get_adjacent_nodes g i in
    List.mem j edges


  let print_edges edges = List.iter (fun (s,t) -> Printf.printf "Edge %d -> %d\n" s t) edges

  let transpose g =
    let edge_list_t = List.map (fun (s,d) -> (d,s)) (get_edgelist g) in
    let transposed_g = init_graph () in
    add_edges edge_list_t transposed_g;
    transposed_g


  let to_undirected g =
    let rec loop edges acc =
      match edges with
      | [] -> acc
      | (s,d)::t ->
        let new_acc = (s,d) :: (d,s) :: acc in
        loop t new_acc
    in
    let undirected_edges = loop (get_edgelist g) [] in
    let undirected_g = init_graph () in
    add_edges undirected_edges undirected_g;
    undirected_g

    let rec chop_off l target =
        match l with
          | [] -> []
          | h::t ->
            if h = target then
              h::t
            else
              chop_off t target

  let detect_cycle g start =
    let nodes = get_nodes g in
    let visited = Hashtbl.create 1000 in
    List.iter (fun node -> Hashtbl.add visited node false) nodes;
    let cycle = ref [] in

    let rec explore g v prev trace =
      Hashtbl.replace visited v true;
      let neighbors = List.filter (fun x -> x <> prev ) (get_adjacent_nodes g v) in
      List.iter (
        fun node ->
          if (Hashtbl.find visited node) then
            (
              if (!cycle = []) then cycle := (chop_off (trace @ [v]) node)
            )
          else
            (
              explore g node v (trace @ [v])
            )
      ) neighbors
    in

    explore g start (0) [];
    !cycle

  let get_edge_dependency edge_list g_tree =
    let edge_dependency = Hashtbl.create 1000 in
    let transposed_g_tree = transpose g_tree in
    List.iter (
      fun (s,d) ->

        let d_out = get_adjacent_nodes g_tree d in
        let d_in_temp = get_adjacent_nodes transposed_g_tree d in
        let d_in = List.filter (fun x -> x <> s) d_in_temp in

        let s_out_temp = get_adjacent_nodes g_tree s in
        let s_out = List.filter (fun x -> x <> d) s_out_temp in
        let s_in = get_adjacent_nodes transposed_g_tree s in

        let all_dependency =
          if ((s_in = [] && s_out = []) || (d_in = [] && d_out = [])) then
            []
          else
            (List.map (fun (x) -> (d,x)) d_out) @
            (List.map (fun (x) -> (x,d)) d_in) @
            (List.map (fun (x) -> (s,x)) s_out) @
            (List.map (fun (x) -> (x,s)) s_in) in
        Hashtbl.add edge_dependency (s,d) all_dependency
    ) edge_list;
    edge_dependency

  let rec more_than_twice l e =
    let rec loop l e acc =
      match l with
      | [] -> false
      | h::t ->
        if (h = e) && (acc) then
          true
        else if (h = e) then
          loop t e true
        else
          loop t e false
    in
    loop l e false

  let find_roots edge_list =
    let from_nodes = List.map (fun (x,y) -> x) edge_list in
    let to_nodes = List.map (fun (x,y) -> y) edge_list in
    let roots = List.filter (fun x -> not (List.mem x to_nodes)) from_nodes in
    roots

  let find_leaves edge_list =
    let from_nodes = List.map (fun (x,y) -> x) edge_list in
    let to_nodes = List.map (fun (x,y) -> y) edge_list in
    let sources = List.filter (fun x -> not (List.mem x to_nodes) && not (more_than_twice from_nodes x)) from_nodes in
    let destinations = List.filter (fun x -> not (List.mem x from_nodes) && not (more_than_twice to_nodes x)) to_nodes in
    (sources, destinations)

end

module Data = struct
  let init_demand l =
    let data_demand = Hashtbl.create 1000 in
    List.iter (fun (node, demand) -> Hashtbl.add data_demand node demand) l;
    data_demand

  let init_cost l =
    let data_cost = Hashtbl.create 1000 in
    List.iter (fun (s,d,cost) -> Hashtbl.add data_cost (s,d) cost) l;
    data_cost

  let demand_at data_demand node = Hashtbl.find data_demand node

  let cost_of data_cost edge = Hashtbl.find data_cost edge

end

module PrimalSolution = struct

  let init_solution edge_list =
    let s = Hashtbl.create 1000 in
    List.iter (fun (x,y) -> Hashtbl.add s (x,y) 0.0) edge_list;
    s


  let update primals amount same opposite =
    List.iter
      (
        fun (i,j) ->
          Printf.printf "In primal update --> (%d,%d) \n" i j;
          let value = Hashtbl.find primals (i,j) in
          Hashtbl.replace primals (i,j) (value +. amount)
      )
      same;
      List.iter
        (
          fun (i,j) ->
            let value = Hashtbl.find primals (i,j) in
            Hashtbl.replace primals (i,j) (value -. amount)
        )
      opposite


  let compute_primal_flow primals g_tree data_demand =
    let transposed_g_tree = Graph.transpose g_tree in
    let edge_list = Graph.get_edgelist g_tree in
    let nodes = Graph.get_nodes g_tree in

    let edge_leave_from = (Hashtbl.create 1000) in
    List.iter (
      fun n ->
        let es = Graph.get_adjacent_nodes g_tree n in
        Hashtbl.add edge_leave_from n es
      )
        nodes ;

    let edge_terminate_at = (Hashtbl.create 1000) in
    List.iter (
      fun n ->
        let es = Graph.get_adjacent_nodes transposed_g_tree n in
        Hashtbl.add edge_terminate_at n es
    )
      nodes ;

    let (sources, destinations) = Graph.find_leaves edge_list in
    let edges_inside = List.filter (fun (s,d) -> not ((List.mem s sources) || (List.mem d destinations))) edge_list in

    List.iter (
      fun s ->
        let d = Hashtbl.find g_tree s in
        let supply = Data.demand_at data_demand s in
        Hashtbl.replace primals (s,d) supply
    ) sources;

    Printf.printf "--------- sources ------\n";
      List.iter (fun x -> Printf.printf "%d\n" x) sources;

    List.iter (
      fun d ->
        let s = Hashtbl.find transposed_g_tree d in
        let demand = Data.demand_at data_demand d in
        Hashtbl.replace primals (s,d) (-.demand)
    ) destinations;

    Printf.printf "--------- destinations ------\n";
    List.iter (fun x -> Printf.printf "%d\n" x) destinations;
    Printf.printf "---------------\n";


    let sol = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) primals [] in
    List.iter (
      fun (s,d,v) -> Printf.printf "(%d, %d) -> %f\n" s d v
    ) sol;

    Printf.printf "-------------------\n";

    let sum_list l = List.fold_left ( +. ) 0. l in
    let to_do_edges = ref edges_inside in

    while (!to_do_edges <> []) do
      let (s,d)::t = !to_do_edges in
      (* Printf.printf "Now this edge --> (%d, %d)\n" s d; *)
      let s_in = Graph.get_adjacent_nodes transposed_g_tree s in
      let s_out = List.filter (fun x -> x <> d) (Graph.get_adjacent_nodes g_tree s) in
      let s_in_es = List.map (fun x -> (x,s)) s_in in
      let s_out_es = List.map (fun x -> (s,x)) s_out in

      let d_in = List.filter (fun x -> x <> s) (Graph.get_adjacent_nodes transposed_g_tree d) in
      let d_out = Graph.get_adjacent_nodes g_tree d in
      let d_in_es = List.map (fun x -> (x,d)) d_in in
      let d_out_es = List.map (fun x -> (d,x)) d_out in


      if (List.for_all (fun (s,d) -> Hashtbl.find primals (s,d) > 0.0) s_in_es) &&
         (List.for_all (fun (s,d) -> Hashtbl.find primals (s,d) > 0.0) s_out_es) then
        (
        let b = Data.demand_at data_demand s in
        let x_out = List.map (fun (s,d) -> Hashtbl.find primals (s,d)) s_out_es in
        let x_out_sum = sum_list x_out in
        let x_in = List.map (fun (s,d) -> Hashtbl.find primals (s,d)) s_in_es in
        let x_in_sum = sum_list x_in in
        let sum = b -. x_out_sum +. x_in_sum in
        Hashtbl.replace primals (s,d) sum;
        to_do_edges := t;
        (* Printf.printf "In the first one: (%d,%d), b = %f sum = %f\n" s d b sum;
        Printf.printf "x_out_sum = %f. x_in_sum = %f\n" x_out_sum x_in_sum *)
        )

      else if (List.for_all (fun (s,d) -> Hashtbl.find primals (s,d) > 0.0) d_in_es) &&
              (List.for_all (fun (s,d) -> Hashtbl.find primals (s,d) > 0.0) d_out_es) then
        (
          let b = Data.demand_at data_demand d in
          let x_out = List.map (fun (s,d) -> Hashtbl.find primals (s,d)) d_out_es in
          let x_out_sum = sum_list x_out in
          let x_in = List.map (fun (s,d) -> Hashtbl.find primals (s,d)) d_in_es in
          let x_in_sum = sum_list x_in in
          let sum = (-.b) +. x_out_sum -. x_in_sum in
          Hashtbl.replace primals (s,d) sum;
          to_do_edges := t;
          Printf.printf "In the second one: (%d,%d), b = %f ,sum = %f\n" s d b sum
        )
      else
        to_do_edges := t @ [(s,d)]

    done

end

module DualSolution = struct

  let init_solution node_list =
    let s = Hashtbl.create 1000 in
    List.iter (fun x -> Hashtbl.add s x 0.0) node_list;
    s

  let update enter enter_val leave leave_val sol =
    Hashtbl.replace sol enter enter_val;
    Hashtbl.replace sol leave leave_val


  let compute_dual duals g_tree data_cost =

    let g_tree_t = Graph.transpose g_tree in
    let roots = Graph.find_roots (Graph.get_edgelist g_tree) in
    let root = List.hd roots in
    Hashtbl.replace duals root 0.0;

    let rec propagate v prev foward =
      let forward_next = List.filter (fun x -> x <> prev)  (Graph.get_adjacent_nodes g_tree v) in
      let backward_next = List.filter (fun x -> x <> prev) (Graph.get_adjacent_nodes g_tree_t v) in
      let y_prev = Hashtbl.find duals prev in

      if foward then
        (
          let c =  Data.cost_of data_cost (prev,v) in
          Hashtbl.replace duals v (y_prev +. c)
        )
      else
        (
          let c = Data.cost_of data_cost (v,prev) in
          Hashtbl.replace duals v (y_prev -. c)
        );

      if (forward_next <> []) then
        (
          List.iter (fun x -> propagate x v true) forward_next
        );

      if (backward_next <> []) then
        (
          List.iter (fun x -> propagate x v false) backward_next
        );

      if (forward_next = [] && backward_next = []) then
        (
          () (* stop *)
        )
    in
    let starting_nodes = Graph.get_adjacent_nodes g_tree root in
    List.iter (fun x -> propagate x root true) starting_nodes

end

module DualSlack = struct

  let init_slack edges =
    let s = Hashtbl.create 1000 in
    List.iter (fun (x,y) -> Hashtbl.add s (x,y) 0.0) edges;
    s

  let compute_slack slacks duals cost non_tree_edges =
    List.iter (
      fun (s,d) ->
        let y_i = Hashtbl.find duals s in
        let y_j = Hashtbl.find duals d in
        let c_ij = Hashtbl.find cost (s,d) in
        let value = y_i +. c_ij -. y_j in
        Hashtbl.replace slacks (s,d) value
    )
    non_tree_edges

end


let check_complementary_slack edges primals slacks =
  let results = List.map
      (fun (i,j) ->
         Printf.printf "check complementarily --> (%d,%d) \n" i j;
         let x_ij = Hashtbl.find primals (i,j) in
         let z_ij = Hashtbl.find slacks (i,j) in
         if (x_ij = 0.0 && z_ij >= 0.0) then
          true
         else
          false
      )
    edges in
  List.for_all (fun b -> b) results

let select_entering_edge non_tree_edges slacks =
  List.hd (List.filter (fun (i,j) -> (Hashtbl.find slacks (i,j)) < 0.0 ) non_tree_edges)

let rec get_edges_from_cycle cycle_nodes acc head =
  match cycle_nodes with
  | [] -> failwith "No nodes in the cycle!"
  | [x] -> acc @ [(x, head)]
  | h1::h2::t -> get_edges_from_cycle (h2::t) (acc @ [(h1,h2)]) head

let rec select_smallest edges_with_flow smallest =
  let (a,b,flow_min) = smallest in
  match edges_with_flow with
  | [] -> failwith "No edge to select!"
  | [(i,j,flow)] ->
    if flow < flow_min then
      (i,j)
    else
      (a,b)

  | (i,j,flow)::t ->
    if flow < flow_min then
      select_smallest t (i,j,flow)
    else
      select_smallest t smallest



let select_leaving_edge g primals entering_edge cycle_nodes =
  let same = ref [] in
  let opposite = ref [] in
  let forwards = ref [] in
  let backwards = ref [] in
  let head = List.hd cycle_nodes in
  let cycle_edges = get_edges_from_cycle cycle_nodes [] head in

  List.iter (
    fun (i,j) ->
      if Graph.check_edge g (i,j) then
        (Printf.printf "Into forward edge --> (%d,%d) \n" i j;
        forwards := (i,j)::!forwards)
      else
        (Printf.printf "Into backward edge --> (%d,%d) \n" j i;
        backwards := (j,i)::!backwards)
  )
    cycle_edges;

  if List.mem entering_edge !forwards then
    (
      same := !forwards;
      opposite := !backwards
    )
  else
    (
      same := !backwards;
      opposite := !forwards
    )
  ;
  let candidate = List.map (fun (i,j) -> (i,j, (Hashtbl.find primals (i,j))) ) !opposite in
  let leaving  = select_smallest candidate (0,0,10000000.0) in
  leaving,!same,!opposite




let main () =

  let edges = [(1,3); (1,4); (1,5); (2,1); (2,3); (2,5); (4,2); (4,5); (6,1); (6,2); (6,3); (6,7); (7,2); (7,5)] in
  let tree_edges = [(1,4); (6,1); (6,2); (2,3); (7,2); (7,5)] in

  let g = Graph.init_graph () in
  let g_tree = Graph.init_graph () in
  Graph.add_edges edges g;
  Graph.add_edges tree_edges g_tree;

  let non_tree_edges = ref [] in
  non_tree_edges := Graph.get_non_tree_edges g g_tree;
  let nodes = Graph.get_nodes g in

  let data_demand = Data.init_demand [(1, 0.0); (2, 0.0); (3, (-.6.0)); (4, (-.6.0)); (5, (-.2.0)); (6, (9.0)); (7, (5.0))] in
  let data_cost = Data.init_cost [(1,3,48.0); (1,4,28.0); (1,5,10.0); (2,1,7.0); (2,3,65.0); (2,5,7.0); (4,2,38.0); (4,5,15.0); (6,1,56.0); (6,2,48.0); (6,3,108.0); (6,7,24.0);(7,2,33.0); (7,5,19.0)] in


  let primals = PrimalSolution.init_solution edges in
  PrimalSolution.compute_primal_flow primals g_tree data_demand;
  let duals = DualSolution.init_solution nodes in
  DualSolution.compute_dual duals g_tree data_cost;
  let slacks = DualSlack.init_slack edges in
  DualSlack.compute_slack slacks duals data_cost !non_tree_edges;

  let entering_edge = ref (0,0) in
  let leaving_edge = ref (0,0) in

  while not (check_complementary_slack !non_tree_edges primals slacks) do

    let tree_edges = Graph.get_edgelist g_tree in
    non_tree_edges := Graph.get_non_tree_edges g g_tree;
    Graph.print_edges tree_edges;

    entering_edge := select_entering_edge !non_tree_edges slacks;

    let (i,j) = !entering_edge in
    Printf.printf "entering edge --> (%d,%d) \n" i j;

    Graph.add_edge !entering_edge g_tree;
    let und_g_tree = Graph.to_undirected g_tree in
    let cycle = Graph.detect_cycle und_g_tree 1 in

    Printf.printf "---------- cycle -------\n";
    List.iter (fun x -> Printf.printf " %d -> " x) cycle;

    Printf.printf "\n-----------------\n";

    let temp,same,opposite = select_leaving_edge g primals !entering_edge cycle in
    leaving_edge := temp;


    let (x,y) = !leaving_edge in
    Printf.printf "leaving edge --> (%d,%d) \n" x y;

    let amount = Hashtbl.find primals !leaving_edge in

    Graph.remove_edge_tree !leaving_edge g_tree;

    PrimalSolution.update primals amount same opposite;
    DualSolution.compute_dual duals g_tree data_cost;


    non_tree_edges := Graph.get_non_tree_edges g g_tree;
    DualSlack.compute_slack slacks duals data_cost !non_tree_edges;


    let sol_primal = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) primals [] in
    List.iter (
      fun (s,d,v) -> Printf.printf "primal (%d, %d) -> %f\n" s d v
    ) sol_primal;

    let sol_dual = Hashtbl.fold (fun node v acc -> (node,v)::acc) duals [] in
    List.iter (
      fun (node,v) -> Printf.printf "dual Node%d -> %f\n" node v
    ) sol_dual;

    let sol_slack = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) slacks [] in
    List.iter (
      fun (s,d,v) -> Printf.printf "slacks (%d, %d) -> %f\n" s d v
    ) sol_slack;

  done





let () = main ()
