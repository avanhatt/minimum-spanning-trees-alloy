open util/integer
open util/natural
open util/ordering[State]
open lib/graph
open MST
open lib/properties

sig State {
	// The graph we're operating on
	g : one UGraph,

	// Clouds
	parentSet : Vertex -> Vertex,

	// Ranks
	ranks : Vertex -> Natural,

	// Edges we haven't tried to add yet
	remainingEdges : set Edge,

	// The edges that we've already added to our MST
	edgesInMST : set Edge
}{
	some g.edges
}

fun minEdges(es : set Edge) : Edge {
	// This returns the set of the edges of the smallest weight if there are multiple
	{e : es | no e2 : es | lt[e2.weight, e.weight]}
}

pred isAddable(e : Edge, pre, post : State) {
	// If they're in different trees, this edge is addable
	no e.v1.^(pre.parentSet) & e.v2.^(pre.parentSet)
/*	no p : Vertex {
		findAndCompress[e.v1, p, pre, post]
		findAndCompress[e.v2, p, pre, post]
	}*/
/*	some disj p1, p2 : Vertex {
		findAndCompress[e.v1, p1, pre, post]
		findAndCompress[e.v2, p2, pre, post]
	}*/
}

fact initialState {
	// Otherwise this will return a spanning forest instead of a spanning tree
	connected[first.g.edges, first.g.vertices]

	// All parent pointers start off pointing to themselves
	all v1, v2 : Vertex |
		v1 -> v2 in first.parentSet iff (v1 = v2) and (v1 in first.g.vertices)

	// Initial ranks are 0
	first.ranks = Vertex -> Zero

	first.remainingEdges = first.g.edges
	no first.edgesInMST
}

fact endState {
	no last.remainingEdges
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	// These all must be operating on the same graph!
	post.g = pre.g

	// Go in order of edge weight
	let minEs = minEdges[pre.remainingEdges] {
		some minE : minEs | {
			isAddable[minE, pre, post] => {
				// Add it to the MST and update the parent pointers
				post.edgesInMST = pre.edgesInMST + minE
				// If r
				some p1: Vertex | findAndCompress[minE.v1, p1, pre, post] | 
				some p2: Vertex | findAndCompress[minE.v2, p2, pre, post]  |
				p1.(pre.ranks) = p2.(pre.ranks) =>{
					// p1 points to p2
					updateRoots[minE.v1, minE.v2, pre, post]
					let curRank = minE.v2.(pre.ranks) | 
						post.ranks = pre.ranks - (minE.v2 -> curRank) + (minE.v2 -> inc[curRank])

				} else { lt[p1.(pre.ranks), p2.(pre.ranks)] => {
					// p1 points to p2                  p1.parent = p2
					updateRoots[minE.v1, minE.v2, pre, post]
					post.ranks = pre.ranks
				
				} else {
					// p2 points to p1
					updateRoots[minE.v2, minE.v1, pre, post]
					post.ranks = pre.ranks			
				}}
			} else {
				// The clouds/MST are still the same
				post.edgesInMST = pre.edgesInMST
				post.parentSet = pre.parentSet
				post.ranks = pre.ranks
			}
			post.remainingEdges = pre.remainingEdges - minE
		}
	}
}

pred updateRoots(v1, v2 : Vertex, pre, post : State) {
	v1 -> v2 in post.parentSet
	let trans1 = v1.^(pre.parentSet) | let trans2 =  v2.^(pre.parentSet) |
		let p1 = v1.(pre.parentSet) | let p2 = v2.(pre.parentSet) |
			let others = Vertex - (trans1 + trans2 + p1 + p2) | 
				let otherRels = (others -> Vertex) & pre.parentSet |
					post.parentSet = ((trans1 - p1) -> p1) + (trans2 -> p2) + (p1 -> p2) + otherRels
}

pred findAndCompress(v, p : Vertex, pre, post : State) {
	p in v.^(pre.parentSet) 
	p -> p in pre.parentSet
	
	all disj v1, v2 : (v.^(pre.parentSet) + v) |
		v1 -> v2 in post.parentSet implies v2 = p
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

/*fact {
	some disj e1, e2 : Edge | e1.weight = e2.weight
}*/

assert findsMST {
	isMST[last.edgesInMST, last.g]
}

run isAddable for 10 Int, 3 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event

//check findsMST for 10 Int, 3 Natural, exactly 3 Edge, 1 Graph, 3 Vertex, 4 State, 3 Event
check findsMST for 10 Int, 3 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event

// run { } for 10 Int, 2 Natural, exactly 3 Edge, 1 Graph, 3 Vertex, 4 State, 3 Event
//run { } for 10 Int, 5 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event
run { } for 10 Int, 9 Natural, exactly 10 Edge, 1 Graph, 5 Vertex, 11 State, 10 Event
