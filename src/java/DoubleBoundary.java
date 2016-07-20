import java.util.*;

public class DoubleBoundary {
	
    ArrayList<Integer> topPath, middlePath, bottomPath;
    Set<Integer> topPartVertices, bottomPartVertices;
    
    private VertexRenamer bottomBoundaryPrepInverse;
    
    private Boundary outerBoundary;
    private VertexRenamer outerBoundaryUncanonizer;
    private String name;
	
    public DoubleBoundary(Boundary topBoundary, Boundary bottomBoundary, String name) {
		VertexRenamer prepBottom = gluingRenamer(topBoundary, bottomBoundary);
		bottomBoundaryPrepInverse = prepBottom.inverseMap();

		Boundary tempBottomBoundary = prepBottom.renamedBoundary(bottomBoundary);
		topPath = topBoundary.getTopPath();
		middlePath = topBoundary.getBottomPath();
		bottomPath = tempBottomBoundary.getBottomPath();

		topPartVertices = new TreeSet<Integer> ();
		topPartVertices.addAll(topPath);
		topPartVertices.addAll(middlePath);
	
		bottomPartVertices = new TreeSet<Integer> ();
		bottomPartVertices.addAll(middlePath);
		bottomPartVertices.addAll(bottomPath);
	
		Boundary outerBoundaryUncanonized = new Boundary(topPath, bottomPath, name + "_outer");
		VertexRenamer outerBoundaryCanonizer = outerBoundaryUncanonized.canonicalRenamer();
		outerBoundary = outerBoundaryUncanonized.canonicalBoundary();
		outerBoundaryUncanonizer = outerBoundaryCanonizer.inverseMap();

		this.name = name;
	}
	
	// Makes a renamer that prepares the bottom boundary to be glued to the top one.
	public VertexRenamer gluingRenamer(Boundary topBoundary, Boundary bottomBoundary) {
		VertexRenamer add100 = bottomBoundary.canonicalRenamer().addX(100);
		Boundary tempBottomBoundary = add100.renamedBoundary(bottomBoundary);
		
		TreeMap<Integer, Integer> newNameList = new TreeMap<Integer, Integer> ();
		for(int i = 0; i < tempBottomBoundary.topPathLength() + 2; ++i) newNameList.put(tempBottomBoundary.topPathVertex(i), topBoundary.bottomPathVertex(i));
		for(int i = 0; i < tempBottomBoundary.bottomPathLength() + 2; ++i)  {
			if(newNameList.containsKey(tempBottomBoundary.bottomPathVertex(i))) {
				newNameList.put(tempBottomBoundary.bottomPathVertex(i), newNameList.get(tempBottomBoundary.bottomPathVertex(i))); 
			} else {
				newNameList.put(tempBottomBoundary.bottomPathVertex(i), tempBottomBoundary.bottomPathVertex(i));
			}
		}	
		
		return add100.compose(new VertexRenamer (newNameList, name + "_gluing"));
	}

	// neighbors in the double boundary
	public Set<Integer> neighbors(Set<Integer> S) {
		Set<Integer> ans = new TreeSet<Integer> ();
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
	public Set<Integer> internalVertices() {
		Set<Integer> ans = new TreeSet<Integer> (middlePath);
		ans.removeAll(topPath);
		ans.removeAll(bottomPath);
		return ans;
	}
	
	public ArrayList<Integer> getTopPath() {return new ArrayList<Integer> (topPath);}
	public ArrayList<Integer> getMiddlePath() {return new ArrayList<Integer> (middlePath);}
	public ArrayList<Integer> getBottomPath() {return new ArrayList<Integer> (bottomPath);}
	
	public Set<Integer> outerToDouble (Set<Integer> S) {return getOuterBoundaryUncanonizer().renamedSet(S);}
	
	public Set<Integer> doubleToTop (Set<Integer> S) {
		TreeSet<Integer> ans = new TreeSet<Integer> (S);
		ans.retainAll(topPartVertices);
		return ans;
	}
	
	public Set<Integer> doubleToBottom (Set<Integer> S) {
		TreeSet<Integer> ans = new TreeSet<Integer> (S);
		ans.retainAll(bottomPartVertices);
		return getBottomBoundaryPrepInverse().renamedSet(ans);
	}	
	
	// Returs a list of input pairs to the original region pair needed to compute the signature of their sum.
	// AddX tells which vertex to add to the middle path, where -1 means dont add anything.
	public List<Pair<InputPair, InputPair> > allInputPairs(InputPair input, int addX) {
		List<Pair<InputPair, InputPair> > ans = new ArrayList<Pair<InputPair, InputPair> > ();
		
		Set<Integer> outerX = new TreeSet<Integer> (input.first);
		Set<Integer> outerD = new TreeSet<Integer> (input.second);
		outerD.removeAll(outerBoundary.neighbors(outerX));
		
		Set<Integer> doubleX = outerToDouble(outerX);
		Set<Integer> doubleD = outerToDouble(outerD);
		if(addX >= 0) {
			if(doubleX.contains(addX)) return ans;
			doubleX.add(addX);
		}
		doubleD.removeAll(neighbors(doubleX));
		
		Set<Integer> topX = doubleToTop(doubleX);
		Set<Integer> bottomX = doubleToBottom(doubleX);
		
		Set<Integer> doubleKnownD = new TreeSet<Integer> (doubleD);
		doubleKnownD.removeAll(middlePath);
		
		// A vertex is unresolved if: (a) it is on the middle path and ((i) it is in D or (ii) it is internal to the double region) 
		// But neighbors of X are automatically resolved.
		TreeSet<Integer> doubleUnresolvedD = new TreeSet<Integer> (doubleD);
		doubleUnresolvedD.retainAll(middlePath); 
		doubleUnresolvedD.addAll(internalVertices()); 
		doubleUnresolvedD.removeAll(neighbors(doubleX)); 

		PowerSet allToTopD = new PowerSet(doubleUnresolvedD);
		for(TreeSet<Integer> S : allToTopD) {
			Set<Integer> resolvedUpD = new TreeSet<Integer> (doubleKnownD);
			resolvedUpD.addAll(S);
			Set<Integer> topD = doubleToTop(resolvedUpD);
			
			Set<Integer> resolvedDownD = new TreeSet<Integer> (doubleUnresolvedD);
			resolvedDownD.removeAll(S);
			resolvedDownD.addAll(doubleKnownD);
			Set<Integer> bottomD = doubleToBottom(resolvedDownD);
			
			InputPair topInput = new InputPair(topX, topD);
			InputPair bottomInput = new InputPair(bottomX, bottomD);
			
			ans.add(new Pair<InputPair, InputPair> (topInput, bottomInput));
		}
		
		return ans;
	}
	
	// Returns the input pairs needed to access in the top and bottom boundaries in order to compute the signature of X,S where
	// these are sets on the outer boundary. These are the pairs where no additional vertices are added to X on the middle path.
	public List<Pair<InputPair, InputPair> > allInputPairsNoX(InputPair input) {return allInputPairs(input, -1);}

	// Returns the input pairs needed to access in the top and bottom boundaries in order to compute the signature of
	// X,S where these are sets on the outer boundary. These are the pairs where one additional vertex is added to X on the
	// middle path - this incurs a cost of 1 that should be added when computing the signature.
	public List<Pair<InputPair, InputPair> > allInputPairsWithX(InputPair input) {
		ArrayList<Pair<InputPair, InputPair> > ans = new ArrayList<Pair<InputPair, InputPair> > ();
		for(int addX : middlePath) {ans.addAll(allInputPairs(input, addX));}
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
			ArrayList<Integer> topBoundaryTopPath, topBoundaryBottomPath, bottomBoundaryTopPath, bottomBoundaryBottomPath;
			
			Scanner sc = new Scanner(System.in);
			
			System.out.println("TopTop / TopBottom / BottomTop / BottomBottom (Boundary / Path length)");
			int tt, tb, bt, bb;
			tt = sc.nextInt();
			tb = sc.nextInt();
			bt = sc.nextInt();
			bb = sc.nextInt();
			
			topBoundaryTopPath = new ArrayList<Integer>();	
			topBoundaryBottomPath = new ArrayList<Integer>();
			bottomBoundaryTopPath = new ArrayList<Integer>();
			bottomBoundaryBottomPath = new ArrayList<Integer>();

			while(tt-->0) {topBoundaryTopPath.add(sc.nextInt());}
			while(tb-->0) {topBoundaryBottomPath.add(sc.nextInt());}
			while(bt-->0) {bottomBoundaryTopPath.add(sc.nextInt());}
			while(bb-->0) {bottomBoundaryBottomPath.add(sc.nextInt());}
				
			Boundary topB = new Boundary(topBoundaryTopPath, topBoundaryBottomPath, "topB");
			Boundary bottomB = new Boundary(bottomBoundaryTopPath, bottomBoundaryBottomPath, "bottomB");

			DoubleBoundary DB = new DoubleBoundary(topB, bottomB, "DB");
			
			System.out.println("Resulting Outer Boundary: ");
			System.out.println(DB.getOuterBoundary());
			
			System.out.println("X length, D length");
			int xl = sc.nextInt();
			int dl = sc.nextInt();
			TreeSet<Integer> X = new TreeSet<Integer> ();
			TreeSet<Integer> D = new TreeSet<Integer> ();
			while(xl-->0) {X.add(sc.nextInt());}
			while(dl-->0) {D.add(sc.nextInt());}
			InputPair inp = new InputPair(X,D);
			
			System.out.println("Input Pairs, no X");
			for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsNoX(inp)) {System.out.println(inpPair);}

			System.out.println("\n Input Pairs, with X");
			for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsWithX(inp)) {System.out.println(inpPair);}
			
			
			sc.close();
	}		
			
			
		
		
}
