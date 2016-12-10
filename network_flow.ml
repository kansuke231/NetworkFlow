
module Graph = struct

  let init_graph () = Hashtbl.create 1000 (* change this value according to the size of the network *)

  let add_edges edge_list g = List.iter (fun (i,j) -> Hashtbl.add g i j) edge_list

  let add_edge edge g = let (i,j) = edge in Hashtbl.add g i j

  let remove_edge_tree edge g_tree =
    let (i,j) = edge in
    let all_nodes = Hashtbl.find_all g_tree i in
    List.iter
      (fun node -> Hashtbl.remove g_tree i) all_nodes; (* First remove everything *)
    List.iter
      (fun node -> if node <> j then Hashtbl.add g_tree i node) all_nodes (* Then put them back except the node j *)

  let get_edgelist g = Hashtbl.fold (fun i j l -> (i,j) :: l) g []

  let get_adjacent_nodes g v = Hashtbl.find_all g v

  let get_nodes g =
    let edge_list = get_edgelist g in
    let nodes_dup = List.fold_left (fun acc (i,j) -> i :: j :: acc) [] edge_list in
    List.sort_uniq compare nodes_dup

  let get_non_tree_edges g g_tree =
    let g_edges = get_edgelist g in
    let g_tree_edges = get_edgelist g_tree in
    List.filter (fun edge -> not (List.mem edge g_tree_edges) ) g_edges

  let check_edge g edge =
    let (i,j) = edge in
    let edges = get_adjacent_nodes g i in
    List.mem j edges

  let print_edges edges = List.iter (fun (i,j) -> Printf.printf "Edge %d -> %d\n" i j) edges

  let transpose g =
    let edge_list_t = List.map (fun (i,j) -> (j,i)) (get_edgelist g) in
    let transposed_g = init_graph () in
    add_edges edge_list_t transposed_g;
    transposed_g

  let to_undirected g =
    let undirected_edges = List.fold_left (fun acc (i,j) -> (i,j)::(j,i)::acc) [] (get_edgelist g) in
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
      let neighbors = List.filter (fun x -> x <> prev) (get_adjacent_nodes g v) in
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
    let from_nodes = List.map (fun (i,j) -> i) edge_list in
    let to_nodes = List.map (fun (i,j) -> j) edge_list in
    List.filter (fun i -> not (List.mem i to_nodes)) from_nodes

  let find_leaves edge_list =
    let from_nodes = List.map (fun (i,j) -> i) edge_list in
    let to_nodes = List.map (fun (i,j) -> j) edge_list in
    let sources = List.filter (fun i -> not (List.mem i to_nodes) && not (more_than_twice from_nodes i)) from_nodes in
    let destinations = List.filter (fun j -> not (List.mem j from_nodes) && not (more_than_twice to_nodes j)) to_nodes in
    (sources, destinations)

  let rec get_edges_from_cycle cycle_nodes acc head =
    match cycle_nodes with
    | [] -> failwith "No nodes in the cycle!"
    | [x] -> acc @ [(x, head)]
    | h1::h2::t -> get_edges_from_cycle (h2::t) (acc @ [(h1,h2)]) head

  let get_component g start =
    let nodes = get_nodes g in
    let visited = Hashtbl.create 1000 in
    List.iter (fun node -> Hashtbl.add visited node false) nodes;

    let rec explore g v =
      Hashtbl.replace visited v true;
      let neighbors = get_adjacent_nodes g v in
      List.iter (
        fun node ->
          if not (Hashtbl.find visited node) then
            (
              explore g node
            )
      ) neighbors
    in

    explore g start;
    Hashtbl.fold (fun key value acc -> (key,value)::acc ) visited []
    |> List.filter (fun (node,check) -> check)
    |> List.map (fun (node,check) -> node)

  let get_disjoint_nodes disjoint_edges entering_edge =
    let (i,j) = entering_edge in
    let g = init_graph () in
    add_edges disjoint_edges g;
    let und_g = to_undirected g in
    let left_group = get_component und_g i in
    let right_group = get_component und_g j in
    (left_group, right_group)


end


module Data = struct

  let init_demand l =
    let data_demand = Hashtbl.create 1000 in
    List.iter (fun (node, demand) -> Hashtbl.add data_demand node demand) l;
    data_demand

  let init_cost l =
    let data_cost = Hashtbl.create 1000 in
    List.iter (fun (i,j,cost) -> Hashtbl.add data_cost (i,j) cost) l;
    data_cost

  let demand_at data_demand node = Hashtbl.find data_demand node

  let cost_of data_cost edge = Hashtbl.find data_cost edge

end


module PrimalSolution = struct

  let init_solution edge_list =
    let solution = Hashtbl.create 1000 in
    List.iter (fun (i,j) -> Hashtbl.add solution (i,j) 0.0) edge_list;
    solution

  let update primals amount same opposite =
    List.iter
      (
        fun (i,j) ->
          let value = Hashtbl.find primals (i,j) in
          Hashtbl.replace primals (i,j) (value +. amount)
      ) same;

    List.iter
      (
        fun (i,j) ->
          let value = Hashtbl.find primals (i,j) in
          Hashtbl.replace primals (i,j) (value -. amount)
      ) opposite

  let compute_primal_flow primals g_tree data_demand =
    let transposed_g_tree = Graph.transpose g_tree in
    let edge_list = Graph.get_edgelist g_tree in
    let nodes = Graph.get_nodes g_tree in

    let edge_leave_from = (Hashtbl.create 1000) in
    List.iter (
      fun n ->
        let es = Graph.get_adjacent_nodes g_tree n in
        Hashtbl.add edge_leave_from n es
    ) nodes ;

    let edge_terminate_at = (Hashtbl.create 1000) in
    List.iter (
      fun n ->
        let es = Graph.get_adjacent_nodes transposed_g_tree n in
        Hashtbl.add edge_terminate_at n es
    ) nodes ;

    let (sources, destinations) = Graph.find_leaves edge_list in
    let edges_inside = List.filter (fun (i,j) -> not ((List.mem i sources) || (List.mem j destinations))) edge_list in

    List.iter (
      fun s ->
        let d = Hashtbl.find g_tree s in
        let supply = Data.demand_at data_demand s in
        Hashtbl.replace primals (s,d) supply
    ) sources;

    List.iter (
      fun d ->
        let s = Hashtbl.find transposed_g_tree d in
        let demand = Data.demand_at data_demand d in
        Hashtbl.replace primals (s,d) (-.demand)
    ) destinations;

    let sum_list l = List.fold_left ( +. ) 0. l in
    let to_do_edges = ref edges_inside in

    while (!to_do_edges <> []) do

      let (i,j) = List.hd !to_do_edges in
      let t = List.tl !to_do_edges in

      let i_in = Graph.get_adjacent_nodes transposed_g_tree i in
      let i_out = List.filter (fun x -> x <> j) (Graph.get_adjacent_nodes g_tree i) in
      let i_in_es = List.map (fun x -> (x,i)) i_in in
      let i_out_es = List.map (fun x -> (i,x)) i_out in

      let j_in = List.filter (fun x -> x <> i) (Graph.get_adjacent_nodes transposed_g_tree j) in
      let j_out = Graph.get_adjacent_nodes g_tree j in
      let j_in_es = List.map (fun x -> (x,j)) j_in in
      let j_out_es = List.map (fun x -> (j,x)) j_out in


      if (List.for_all (fun (i,j) -> Hashtbl.find primals (i,j) > 0.0) i_in_es) &&
         (List.for_all (fun (i,j) -> Hashtbl.find primals (i,j) > 0.0) i_out_es) then
        (
          let b = Data.demand_at data_demand i in
          let x_out = List.map (fun (i,j) -> Hashtbl.find primals (i,j)) i_out_es in
          let x_out_sum = sum_list x_out in
          let x_in = List.map (fun (i,j) -> Hashtbl.find primals (i,j)) i_in_es in
          let x_in_sum = sum_list x_in in
          let sum = b -. x_out_sum +. x_in_sum in
          Hashtbl.replace primals (i,j) sum;
          to_do_edges := t
        )

      else if (List.for_all (fun (i,j) -> Hashtbl.find primals (i,j) > 0.0) j_in_es) &&
              (List.for_all (fun (i,j) -> Hashtbl.find primals (i,j) > 0.0) j_out_es) then
        (
          let b = Data.demand_at data_demand j in
          let x_out = List.map (fun (i,j) -> Hashtbl.find primals (i,j)) j_out_es in
          let x_out_sum = sum_list x_out in
          let x_in = List.map (fun (i,j) -> Hashtbl.find primals (i,j)) j_in_es in
          let x_in_sum = sum_list x_in in
          let sum = (-.b) +. x_out_sum -. x_in_sum in
          Hashtbl.replace primals (i,j) sum;
          to_do_edges := t
        )
      else
        to_do_edges := t @ [(i,j)]

    done

end


module DualSolution = struct

  let init_solution node_list =
    let solution = Hashtbl.create 1000 in
    List.iter (fun x -> Hashtbl.add solution x 0.0) node_list;
    solution

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
    let solution = Hashtbl.create 1000 in
    List.iter (fun (i,j) -> Hashtbl.add solution (i,j) 0.0) edges;
    solution

  let compute_slack slacks duals cost non_tree_edges =
    List.iter (
      fun (i,j) ->
        let y_i = Hashtbl.find duals i in
        let y_j = Hashtbl.find duals j in
        let c_ij = Hashtbl.find cost (i,j) in
        let value = y_i +. c_ij -. y_j in
        Hashtbl.replace slacks (i,j) value
    ) non_tree_edges

  let update slacks amount same opposite =
    List.iter (fun (i,j) ->
        let value = Hashtbl.find slacks (i,j) in
        Hashtbl.replace slacks (i,j) (value -. amount)
      ) same;

      List.iter (fun (i,j) ->
          let value = Hashtbl.find slacks (i,j) in
          Hashtbl.replace slacks (i,j) (value +. amount)
        ) opposite;
end


let check_complementary_slack edges primals slacks =
  let results = List.map
      (fun (i,j) ->
         let x_ij = Hashtbl.find primals (i,j) in
         let z_ij = Hashtbl.find slacks (i,j) in
         if (x_ij = 0.0 && z_ij >= 0.0) then true else false
      ) edges in
  List.for_all (fun b -> b) results


let select_entering_edge non_tree_edges slacks =
  List.hd (List.filter (fun (i,j) -> (Hashtbl.find slacks (i,j)) < 0.0 ) non_tree_edges)


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
  let cycle_edges = Graph.get_edges_from_cycle cycle_nodes [] head in

  List.iter (
    fun (i,j) ->
      if Graph.check_edge g (i,j) then
        forwards := (i,j)::!forwards
      else
        backwards := (j,i)::!backwards
  ) cycle_edges;

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

let objective primals costs =
  let obj = Hashtbl.fold (fun (i,j) flow l -> (i,j,flow) :: l) primals []
             |> List.filter (fun (i,j,flow) -> flow > 0.0)
             |> List.map (fun (i,j,flow) -> let cost = Hashtbl.find costs (i,j) in cost *. flow)
             |> List.fold_left ( +. ) 0.
  in
  if obj = 0.0 then true else false



let solve primals duals slacks g g_tree non_tree_edges costs demands =
  let entering_edge = ref (0,0) in
  let leaving_edge = ref (0,0) in

  while not (check_complementary_slack !non_tree_edges primals slacks) do

    let tree_edges = Graph.get_edgelist g_tree in
    non_tree_edges := Graph.get_non_tree_edges g g_tree;

    Printf.printf "Tree solution is: \n";
    Graph.print_edges tree_edges;

    Printf.printf "Non-tree edges:\n";
    Graph.print_edges !non_tree_edges;

    let sol_slacks = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) slacks [] in
    List.iter (
      fun (s,d,v) -> Printf.printf "sol_slacks (%d, %d) -> %f\n" s d v
    ) sol_slacks;

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
    let slack_amount = Hashtbl.find slacks !entering_edge in

    Graph.remove_edge_tree !leaving_edge g_tree;
    non_tree_edges := Graph.get_non_tree_edges g g_tree;

    let disjoint_edges = List.filter (fun (i,j) -> (i,j) <> !entering_edge) (Graph.get_edgelist g_tree) in
    let (left_group,right_group) = Graph.get_disjoint_nodes disjoint_edges !entering_edge in

    (* slack edges that bridge the two dijoint component with the same direction as the entering *)
    let bridge_same = List.filter (fun (i,j) -> (List.mem i left_group)&&(List.mem j right_group)) !non_tree_edges in

    (* slack edges that bridge the two dijoint component with the opposite direction of the entering *)
    let bridge_opposite = List.filter (fun (i,j) -> (List.mem j left_group)&&(List.mem i right_group)) !non_tree_edges in

    PrimalSolution.update primals amount same opposite;
    (* DualSolution.compute_dual duals g_tree costs; *)

    DualSlack.update slacks slack_amount (!entering_edge::bridge_same) bridge_opposite;


  done;
  primals

let phase1 edges demands =
  let transit = -1 in
  let g = Graph.init_graph () in
  Graph.add_edges edges g;

  let nodes = transit::(Graph.get_nodes g) in

  let data_demand = Data.init_demand ((transit, 0.0)::demands) in

  (* let supplyers_temp = List.filter (fun (node,demand) -> if demand > 0.0 then true else false) demands
                  |> List.map (fun (node, demand) -> node) in

  let consumers = List.filter (fun (node,demand) -> if demand <= 0.0 then true else false) demands
                  |> List.map (fun (node, demand) -> node) in *)

  let supplyers = List.filter (fun (node,demand) -> if demand > 0.0 then true else false) demands
                       |> List.map (fun (node, demand) -> node) in

  let consumers = List.filter (fun (node,demand) -> if demand <= 0.0 && node <> transit then true else false) demands
                  |> List.map (fun (node, demand) -> node) in



  let artificial_edges = (List.map (fun s -> (s,transit)) supplyers) @ ((List.map (fun c -> (transit,c)) consumers)) in

  let additional_edges = List.filter (fun (i,j) -> not (List.mem (i,j) edges)) artificial_edges in
  let non_tree_edges = ref [] in
  non_tree_edges := List.filter (fun (i,j) -> not (List.mem (i,j) artificial_edges)) edges;


  (* adde only edges not in the original edge list *)
  Graph.add_edges additional_edges g;
  let g_tree = Graph.init_graph () in
  Graph.add_edges artificial_edges g_tree;

  (* if an edge is in both original and artificial, consider it as an artificial *)
  let costs_original = List.filter (fun (i,j) -> not (List.mem (i,j) artificial_edges)) edges
                       |> List.map (fun (i,j) -> (i,j,0.0)) in
  let costs_artificial = List.map (fun (i,j) -> (i,j,1.0)) artificial_edges in
  let data_cost = Data.init_cost (costs_original @ costs_artificial) in

  let primals = PrimalSolution.init_solution (edges @ additional_edges) in
  PrimalSolution.compute_primal_flow primals g_tree data_demand;

  let duals = DualSolution.init_solution nodes in
  DualSolution.compute_dual duals g_tree data_cost;

  let slacks = DualSlack.init_slack (edges @ additional_edges) in
  DualSlack.compute_slack slacks duals data_cost !non_tree_edges;

  Printf.printf "------- g tree --\n";
  Graph.print_edges (Graph.get_edgelist g_tree);
  Printf.printf "---------\n";

  Printf.printf "------- g --\n";
  Graph.print_edges (Graph.get_edgelist g);
  Printf.printf "---------\n";


  let answer_primal = solve primals duals slacks g g_tree non_tree_edges data_cost data_demand in

  if objective answer_primal data_cost then
    answer_primal
  else
    failwith "The network is infeasible"



let main () =

  let edges = [(1,3); (1,4); (1,5); (2,1); (2,3); (2,5); (4,2); (4,5); (6,1); (6,2); (6,3); (6,7); (7,2); (7,5)] in
  let demands = [(1, 0.0); (2, 0.0); (3, (-.6.0)); (4, (-.6.0)); (5, (-.2.0)); (6, (9.0)); (7, (5.0))] in
  let costs = [(1,3,48.0); (1,4,28.0); (1,5,10.0); (2,1,7.0); (2,3,65.0); (2,5,7.0); (4,2,38.0); (4,5,15.0); (6,1,56.0); (6,2,48.0); (6,3,108.0); (6,7,24.0);(7,2,33.0); (7,5,19.0)] in

  let tree_edges = [(1,4); (6,1); (6,2); (2,3); (7,2); (7,5)] in

  let g = Graph.init_graph () in
  let g_tree = Graph.init_graph () in
  Graph.add_edges edges g;
  Graph.add_edges tree_edges g_tree;

  let non_tree_edges = ref [] in
  non_tree_edges := Graph.get_non_tree_edges g g_tree;
  let nodes = Graph.get_nodes g in

  let data_demand = Data.init_demand demands in
  let data_cost = Data.init_cost costs in


  let primals = PrimalSolution.init_solution edges in
  PrimalSolution.compute_primal_flow primals g_tree data_demand;
  let duals = DualSolution.init_solution nodes in
  DualSolution.compute_dual duals g_tree data_cost;
  let slacks = DualSlack.init_slack edges in
  DualSlack.compute_slack slacks duals data_cost !non_tree_edges;



  let answer_primal =   phase1 edges demands in (* solve primals duals slacks g g_tree non_tree_edges data_cost data_demand in   *)

  let sol_primal = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) primals [] in
  List.iter (
    fun (s,d,v) -> Printf.printf "primals primal (%d, %d) -> %f\n" s d v
  ) sol_primal;

  let sol_slacks = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) slacks [] in
  List.iter (
    fun (s,d,v) -> Printf.printf "slacks (%d, %d) -> %f\n" s d v
  ) sol_slacks;

  let sol_primal_answer = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) answer_primal [] in
  List.iter (
    fun (s,d,v) -> Printf.printf "answer_primal primal (%d, %d) -> %f\n" s d v
  ) sol_primal_answer



let () = main ()
