import java.util.*;

public class DoubleBoundary {
	
    Path topPath, middlePath, bottomPath;
    Set<Vertex> topPartVertices, bottomPartVertices;
    
    private VertexRenamer bottomBoundaryPrepInverse;
    
    private Boundary outerBoundary;
    private VertexRenamer outerBoundaryUncanonizer;
    private String name;
	
    public DoubleBoundary(Boundary topBoundary, Boundary bottomBoundary) {
		VertexRenamer prepBottom = gluingRenamer(topBoundary, bottomBoundary);
		bottomBoundaryPrepInverse = prepBottom.inverseMap();

		Boundary tempBottomBoundary = prepBottom.renamedBoundary(bottomBoundary);
		topPath = topBoundary.getTopPath();
		middlePath = topBoundary.getBottomPath();
		bottomPath = tempBottomBoundary.getBottomPath();

		topPartVertices = new TreeSet<Vertex> ();
		topPartVertices.addAll(topPath.asArrayList());
		topPartVertices.addAll(middlePath.asArrayList());
	
		bottomPartVertices = new TreeSet<Vertex> ();
		bottomPartVertices.addAll(middlePath.asArrayList());
		bottomPartVertices.addAll(bottomPath.asArrayList());
	
		Boundary outerBoundaryUncanonized = new Boundary(topPath, bottomPath);
		VertexRenamer outerBoundaryCanonizer = outerBoundaryUncanonized.canonicalRenamer();
		outerBoundary = outerBoundaryUncanonized.canonicalBoundary();
		outerBoundaryUncanonizer = outerBoundaryCanonizer.inverseMap();

		this.name = name;
	}
	
	// Makes a renamer that prepares the bottom boundary to be glued to the top one.
	public VertexRenamer gluingRenamer(Boundary topBoundary, Boundary bottomBoundary) {
		VertexRenamer add100 = bottomBoundary.canonicalRenamer().addX(100);
		Boundary tempBottomBoundary = add100.renamedBoundary(bottomBoundary);
		
		TreeMap<Vertex, Vertex> newNameList = new TreeMap<Vertex, Vertex> ();
		for(int i = 0; i < tempBottomBoundary.topPathLength().toInt + 2; ++i) newNameList.put(tempBottomBoundary.topPathVertex(i), topBoundary.bottomPathVertex(i));
		for(int i = 0; i < tempBottomBoundary.bottomPathLength().toInt + 2; ++i)  {
			if(newNameList.containsKey(tempBottomBoundary.bottomPathVertex(i))) {
				newNameList.put(tempBottomBoundary.bottomPathVertex(i), newNameList.get(tempBottomBoundary.bottomPathVertex(i))); 
			} else {
				newNameList.put(tempBottomBoundary.bottomPathVertex(i), tempBottomBoundary.bottomPathVertex(i));
			}
		}	
		
		return add100.compose(new VertexRenamer (newNameList));
	}

	// neighbors in the double boundary
	public Set<Vertex> neighbors(Set<Vertex> S) {
		Set<Vertex> ans = new TreeSet<Vertex> ();
		ans = PathOperator.pathNeighbors(topPath, S);	
		ans.addAll(PathOperator.pathNeighbors(middlePath, S));
		ans.addAll(PathOperator.pathNeighbors(bottomPath, S));
		return ans;
	}
	
	// Produces the outer boundary canonized
	public Boundary getOuterBoundary() {return outerBoundary;}
	
	// outputs the reverse renaming maps
	public VertexRenamer getBottomBoundaryPrepInverse() {return bottomBoundaryPrepInverse;}
	public VertexRenamer getOuterBoundaryUncanonizer() {return outerBoundaryUncanonizer;}
	
	// Outputs the internal middle path vertices
	public Set<Vertex> internalVertices() {
	    Set<Vertex> ans = new TreeSet<Vertex> (middlePath.asArrayList());
	    ans.removeAll(topPath.asArrayList());
	    ans.removeAll(bottomPath.asArrayList());
	    return ans;
	}
	
	public Path getTopPath() {return new Path(topPath);}
	public Path getMiddlePath() {return new Path (middlePath);}
	public Path getBottomPath() {return new Path (bottomPath);}
	
	public Set<Vertex> outerToDouble (Set<Vertex> S) {return getOuterBoundaryUncanonizer().renamedSet(S);}
	
	public Set<Vertex> doubleToTop (Set<Vertex> S) {
		TreeSet<Vertex> ans = new TreeSet<Vertex> (S);
		ans.retainAll(topPartVertices);
		return ans;
	}
	
	public Set<Vertex> doubleToBottom (Set<Vertex> S) {
		TreeSet<Vertex> ans = new TreeSet<Vertex> (S);
		ans.retainAll(bottomPartVertices);
		return getBottomBoundaryPrepInverse().renamedSet(ans);
	}	
	
	// Returs a list of input pairs to the original region pair needed to compute the signature of their sum.
	// AddX tells which vertex to add to the middle path, where null means dont add anything.
	public List<Pair<InputPair, InputPair> > allInputPairs(InputPair input, Vertex addX) {
		List<Pair<InputPair, InputPair> > ans = new ArrayList<Pair<InputPair, InputPair> > ();
		
		Set<Vertex> outerX = new TreeSet<Vertex> (input.first);
		Set<Vertex> outerD = new TreeSet<Vertex> (input.second);
		outerD.removeAll(outerBoundary.neighbors(outerX));
		
		Set<Vertex> doubleX = outerToDouble(outerX);
		Set<Vertex> doubleD = outerToDouble(outerD);
		if(addX != null) {
		    if(doubleX.contains(addX)) return ans;
		    doubleX.add(addX);
		}
		doubleD.removeAll(neighbors(doubleX));
		
		Set<Vertex> topX = doubleToTop(doubleX);
		Set<Vertex> bottomX = doubleToBottom(doubleX);
		
		Set<Vertex> doubleKnownD = new TreeSet<Vertex> (doubleD);
		doubleKnownD.removeAll(middlePath.asArrayList());
		
		// A vertex is unresolved if: (a) it is on the middle path and ((i) it is in D or (ii) it is internal to the double region) 
		// But neighbors of X are automatically resolved.
		TreeSet<Vertex> doubleUnresolvedD = new TreeSet<Vertex> (doubleD);
		doubleUnresolvedD.retainAll(middlePath.asArrayList()); 
		doubleUnresolvedD.addAll(internalVertices()); 
		doubleUnresolvedD.removeAll(neighbors(doubleX)); 

		PowerSet<Vertex> allToTopD = new PowerSet<Vertex>(doubleUnresolvedD);
		for(TreeSet<Vertex> S : allToTopD) {
			Set<Vertex> resolvedUpD = new TreeSet<Vertex> (doubleKnownD);
			resolvedUpD.addAll(S);
			Set<Vertex> topD = doubleToTop(resolvedUpD);
			
			Set<Vertex> resolvedDownD = new TreeSet<Vertex> (doubleUnresolvedD);
			resolvedDownD.removeAll(S);
			resolvedDownD.addAll(doubleKnownD);
			Set<Vertex> bottomD = doubleToBottom(resolvedDownD);
			
			InputPair topInput = new InputPair(topX, topD);
			InputPair bottomInput = new InputPair(bottomX, bottomD);
			
			ans.add(new Pair<InputPair, InputPair> (topInput, bottomInput));
		}
		
		return ans;
	}
	
	// Returns the input pairs needed to access in the top and bottom boundaries in order to compute the signature of X,S where
	// these are sets on the outer boundary. These are the pairs where no additional vertices are added to X on the middle path.
	public List<Pair<InputPair, InputPair> > allInputPairsNoX(InputPair input) {return allInputPairs(input, null);}

	// Returns the input pairs needed to access in the top and bottom boundaries in order to compute the signature of
	// X,S where these are sets on the outer boundary. These are the pairs where one additional vertex is added to X on the
	// middle path - this incurs a cost of 1 that should be added when computing the signature.
	public List<Pair<InputPair, InputPair> > allInputPairsWithX(InputPair input) {
		ArrayList<Pair<InputPair, InputPair> > ans = new ArrayList<Pair<InputPair, InputPair> > ();
		for(Vertex addX : middlePath.asArrayList()) {ans.addAll(allInputPairs(input, addX));}
		return ans;
	}
	
    public List<Pair<InputPair, InputPair> > allInputPairsMaybeX(boolean X, InputPair input) {
	if (X)
	    return allInputPairsWithX(input);
	else
	    return allInputPairsNoX(input);
    }
	public String toString() {return "<" + topPath.toString() + " - " + middlePath.toString() + " - " + bottomPath.toString() + ">";}
	
	// -------------------- TESTING
	public static void main(String[] args) {
			ArrayList<Vertex> topBoundaryTopPath, topBoundaryBottomPath, bottomBoundaryTopPath, bottomBoundaryBottomPath;
			
			Scanner sc = new Scanner(System.in);
			
			System.out.println("TopTop / TopBottom / BottomTop / BottomBottom (Boundary / Path length)");
			int tt, tb, bt, bb;
			tt = sc.nextInt();
			tb = sc.nextInt();
			bt = sc.nextInt();
			bb = sc.nextInt();
			
			topBoundaryTopPath = new ArrayList<Vertex>();	
			topBoundaryBottomPath = new ArrayList<Vertex>();
			bottomBoundaryTopPath = new ArrayList<Vertex>();
			bottomBoundaryBottomPath = new ArrayList<Vertex>();

			while(tt-->0) {topBoundaryTopPath.add(new Vertex(sc.nextInt()));}
			while(tb-->0) {topBoundaryBottomPath.add(new Vertex(sc.nextInt()));}
			while(bt-->0) {bottomBoundaryTopPath.add(new Vertex(sc.nextInt()));}
			while(bb-->0) {bottomBoundaryBottomPath.add(new Vertex(sc.nextInt()));}
				
			Boundary topB = new Boundary(new Path(topBoundaryTopPath), new Path(topBoundaryBottomPath));
			Boundary bottomB = new Boundary(new Path(bottomBoundaryTopPath), new Path(bottomBoundaryBottomPath));

			DoubleBoundary DB = new DoubleBoundary(topB, bottomB);
			
			System.out.println("Resulting Outer Boundary: ");
			System.out.println(DB.getOuterBoundary());
			
			System.out.println("X length, D length");
			int xl = sc.nextInt();
			int dl = sc.nextInt();
			TreeSet<Vertex> X = new TreeSet<Vertex> ();
			TreeSet<Vertex> D = new TreeSet<Vertex> ();
			while(xl-->0) {X.add(new Vertex(sc.nextInt()));}
			while(dl-->0) {D.add(new Vertex(sc.nextInt()));}
			InputPair inp = new InputPair(X,D);
			
			System.out.println("Input Pairs, no X");
			for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsNoX(inp)) {System.out.println(inpPair);}

			System.out.println("\n Input Pairs, with X");
			for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsWithX(inp)) {System.out.println(inpPair);}
			
			
			sc.close();
	}		
			
			
		
		
}
