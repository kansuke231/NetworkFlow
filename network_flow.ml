
module Graph = struct

  let init_graph () = Hashtbl.create 1000 (* change this value according to the size of the network *)

  let add_edges edge_list g = List.iter (fun (s,d) -> Hashtbl.add g s d) edge_list

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

    explore g start (-1) [];
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


  let update enter enter_val leave leave_val sol =
    Hashtbl.replace sol enter enter_val;
    Hashtbl.replace sol leave leave_val


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
    let neither = List.filter (fun x -> not (List.mem x sources) && not (List.mem x destinations)) nodes in
    let edge_dependency = Graph.get_edge_dependency edge_list g_tree in


    List.iter (
      fun s ->
        let d = Hashtbl.find g_tree s in
        let supply = Data.demand_at data_demand s in
        Hashtbl.replace primals (s,d) supply
    ) sources;

    Printf.printf "--------- sources ------\n";
      List.iter (fun x -> Printf.printf "%c\n" x) sources;
    Printf.printf "---------------\n";

    List.iter (
      fun d ->
        let s = Hashtbl.find transposed_g_tree d in
        let demand = Data.demand_at data_demand d in
        Hashtbl.replace primals (s,d) (-.demand)
    ) destinations;

    Printf.printf "--------- destinations ------\n";
      List.iter (fun x -> Printf.printf "%c\n" x) destinations;
    Printf.printf "---------------\n";

    Printf.printf "-------------------\n";

    let sol = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) primals [] in
    List.iter (
      fun (s,d,v) -> Printf.printf "(%c, %c) -> %f\n" s d v
    ) sol;

    Printf.printf "-------------------\n";

    let sum_list l = List.fold_left ( +. ) 0. l in
    let to_do_edges = ref edges_inside in

    while (!to_do_edges <> []) do
      let (s,d)::t = !to_do_edges in
      Printf.printf "Now this edge --> (%c, %c)\n" s d;
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
        Printf.printf "In the first one: (%c,%c), b = %f sum = %f\n" s d b sum;
        Printf.printf "x_out_sum = %f. x_in_sum = %f\n" x_out_sum x_in_sum
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
          Printf.printf "In the second one: (%c,%c), b = %f ,sum = %f\n" s d b sum
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
    let nodes = Graph.get_nodes g_tree in
    let roots = Graph.find_roots (Graph.get_edgelist g_tree) in
    let root = List.hd roots in
    Hashtbl.replace duals root 0.0;

    let rec propagate v prev foward =
      let forward_next = List.filter (fun x -> x <> prev)  (Graph.get_adjacent_nodes g_tree v) in
      let backward_next = List.filter (fun x -> x <> prev) (Graph.get_adjacent_nodes g_tree_t v) in
      let y_v = Hashtbl.find duals v in
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



let main () =
  let edges = [('a','d'); ('f','a'); ('f','b'); ('b','c'); ('g','b'); ('g','e')] in
  let g = Graph.init_graph () in
  Graph.add_edges edges g;
  let nodes = Graph.get_nodes g in
  let data_demand = Data.init_demand [('a', 0.0); ('b', 0.0); ('c', (-.6.0)); ('d', (-.6.0)); ('e', (-.2.0)); ('f', (9.0)); ('g', (5.0))] in
  let data_cost = Data.init_cost [('a','d',28.0); ('f','a',56.0); ('f','b',48.0); ('b','c',65.0); ('g','b',33.0); ('g','e',19.0)] in
  let primals = PrimalSolution.init_solution edges in
  PrimalSolution.compute_primal_flow primals g data_demand;
  let duals = DualSolution.init_solution nodes in
  DualSolution.compute_dual duals g data_cost;

  let sol_primal = Hashtbl.fold (fun (s,d) v acc -> (s,d,v)::acc) primals [] in
  List.iter (
    fun (s,d,v) -> Printf.printf "(%c, %c) -> %f\n" s d v
  ) sol_primal;

  let sol_dual = Hashtbl.fold (fun node v acc -> (node,v)::acc) duals [] in
  List.iter (
    fun (node,v) -> Printf.printf "Node%c -> %f\n" node v
  ) sol_dual

  (* let und_g = Graph.to_undirected g in
  let cycle = Graph.detect_cycle und_g 1 in
  List.iter (fun x -> Printf.printf " %d ->" x) cycle *)


let () = main ()
