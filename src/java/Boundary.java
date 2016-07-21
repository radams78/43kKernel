import java.util.*;
import java.io.*;

/**
 * A <i>boundary</i> consists of:
 * <ul>
 * <li>a <i>top path</i> as a list of points.
 * <li>a <i>bottom path</i> as a list of points.
 * </ul>
 * Points are represented as integers.  
 *
 * Invariant: The top and bottom paths should have common end-points, called <i>anchors</i>.
 */
public class Boundary {
    static final String COQTYPE = "Boundary";

    private ArrayList<Integer> topPath;
    private ArrayList<Integer> bottomPath;
    /** Number of vertices in both paths, including end-points. */
    public final int size;
    private String name;

    /**
     * Precondition: topPath and bottomPath have the same first and last elements
     */
    public Boundary(ArrayList<Integer> topPath, ArrayList<Integer> bottomPath) {
	assert topPath.get(0) == bottomPath.get(0);
	assert topPath.get(topPath.size() - 1) == bottomPath.get(bottomPath.size() - 1);
	this.topPath = new ArrayList<Integer> (topPath);
	this.bottomPath = new ArrayList<Integer> (bottomPath);
	this.size = vertexSet().size();
	this.name = name;
    } 
	
    /** Set of vertices in both paths, including end-points, in order: top path from left to right, then (bottom path - top path) from left to right. */
    public ArrayList<Integer> vertexSet() {
	ArrayList<Integer> ans = new ArrayList<Integer> (topPath);
	for(int i = 0; i < bottomPath.size(); ++i) {
	    if(ans.contains(bottomPath.get(i))) continue;
	    ans.add(bottomPath.get(i));
	}
	return ans;	
    }
    
    /** Set of all neigbours of a given set of points */
    public Set<Integer> neighbors(Set<Integer> S) {
	Set<Integer> ans = PathOperator.pathNeighbors(topPath, S);	
	ans.addAll(PathOperator.pathNeighbors(bottomPath, S));
	return ans;
    }
    
    /** Tests whether two points are neighbours in the boundary */
    public boolean areNeighbors(int u, int v) {
	Set<Integer> S = new TreeSet<Integer> ();
	S.add(u);
	return neighbors(S).contains(v);
    }
    
    public int topPathLength() {return topPath.size() - 2;}
    public int bottomPathLength() {return bottomPath.size() - 2;}
    
    public int leftAnchor() {return topPath.get(0);}
    public int rightAnchor() {return topPath.get(topPath.size() - 1);}
    public Set<Integer> getAnchors() {
	Set<Integer> ans = new TreeSet<Integer> ();
	ans.add(leftAnchor());
	ans.add(rightAnchor());
	return ans;
    }
    
	public int topPathVertex(int p) {return topPath.get(p);}
    public int bottomPathVertex(int p) {return bottomPath.get(p);}
    
    public ArrayList<Integer> getTopPath(){return new ArrayList<Integer> (topPath);}
    public ArrayList<Integer> getBottomPath(){return new ArrayList<Integer> (bottomPath);}
    
    /** Renumbers the vertices in the order given by {@link #vertexSet} */
    public VertexRenamer canonicalRenamer() {return new VertexRenamer(vertexSet());}
    /** The boundary, as renumbered by {@link #canonicalRenamer} */
    Boundary canonicalBoundary() {return canonicalRenamer().renamedBoundary(this);}
    
    public String toString() {return "<" + topPath.toString() + " - " + bottomPath.toString() + ">";}
    
    public boolean equals(Object o) {
	if(!(o instanceof Boundary)) return false;
	Boundary b = (Boundary) o;
	return topPath.equals(b.getTopPath()) && bottomPath.equals(b.getBottomPath());
	}
    
    /** An input (D, X) is valid if D is disjoint from N(X) */
    public ArrayList<InputPair> allValidInputs() {
	ArrayList<InputPair> ans = new ArrayList<InputPair> ();
	TreeSet<Integer> allVertices = new TreeSet<Integer> (vertexSet());
	PowerSet allVertexSubsets = new PowerSet(allVertices);
	for(TreeSet<Integer> X : allVertexSubsets) {
	    TreeSet<Integer> possibleD = new TreeSet<Integer> (allVertices);
	    possibleD.removeAll(neighbors(X));
	    PowerSet allD = new PowerSet(possibleD);
	    for(TreeSet<Integer> D : allD) {
		ans.add(new InputPair(X,D));
	    }
	}
	return ans;
    }
    
    /** true if b can be glued to the bottom of this */
    public boolean canGlue(Boundary bottomBoundary) {
	
	// FALSE if top and bottom boundaries dont match
	if(bottomPathLength() != bottomBoundary.topPathLength()) return false;
	
	// FALSE if gluing creates a double edge on top and bottom that is not an edge in middle.
	DoubleBoundary DB = preglue(bottomBoundary);
	List<Pair<Integer, Integer> > forbiddenEdges = PathOperator.pathEdges(DB.getTopPath());
	forbiddenEdges.retainAll(PathOperator.pathEdges(DB.getBottomPath()));
	forbiddenEdges.removeAll(PathOperator.pathEdges(DB.getMiddlePath()));
	if(!forbiddenEdges.isEmpty()) return false;
	
	return true;	
    }
    
    public DoubleBoundary preglue(Boundary bottomBoundary) {return new DoubleBoundary(this, bottomBoundary);}

    /** glue bottomBoundary onto this and return the resulting outer boundary */
    public Boundary glue(Boundary bottomBoundary) {return preglue(bottomBoundary).getOuterBoundary();}
    
    
    /** Transforms an input pair to Johan Style (i.e (X,S) where S = VertexSet \ (N[X] u D) */
	public InputPair toJohanStyle(InputPair inp) {
	    Set<Integer> X = new TreeSet<Integer> (inp.first);
	    Set<Integer> D = new TreeSet<Integer> (inp.second);
	    Set<Integer> NX = neighbors(X);
	    
	    Set<Integer> S = new TreeSet<Integer> (vertexSet());
	    S.removeAll(NX);
	    S.removeAll(D);
	    
	    return new InputPair(X,S);
	}
    
    /** Transforms an input pair from Johan Style to Daniel Style
     * (X,S) --> (X, D) where D = VertexSet \ (N[X] u D) 
     * so ironically converting to and from is the same. */
    public InputPair fromJohanStyle(InputPair inp) {return toJohanStyle(inp);}
    
    
    // TESTING
    public static void main(String[] args) {
	ArrayList<Integer> topBoundaryTopPath, topBoundaryBottomPath;
	
	Scanner sc = new Scanner(System.in);
	
	System.out.println("Name");
	String name = sc.nextLine();

	System.out.println("Top / Bottom (Path length)");
	int tt, tb;
	tt = sc.nextInt();
	tb = sc.nextInt();
	
	topBoundaryTopPath = new ArrayList<Integer>();	
	topBoundaryBottomPath = new ArrayList<Integer>();
	
	while(tt-->0) {topBoundaryTopPath.add(sc.nextInt());}
	while(tb-->0) {topBoundaryBottomPath.add(sc.nextInt());}
	
	Boundary topB = new Boundary(topBoundaryTopPath, topBoundaryBottomPath);
	
	System.out.println("Resulting Boundary: ");
	System.out.println(topB);
	
	System.out.println("Canonical Form Boundary: ");
	System.out.println(topB.canonicalBoundary());
	
	System.out.println("All valid inputs");
	for(InputPair P : topB.allValidInputs()) {System.out.println(P);}
	
	sc.close();
    }

    public CoqObject toCoq() {
	String definition = "mkBoundary nat \n  ";
	definition += CoqObject.coqListInteger(topPath);
	definition += " \n  ";
	definition += CoqObject.coqListInteger(bottomPath); //TODO Duplication
	return new CoqObject(COQTYPE, definition);
    }
}
