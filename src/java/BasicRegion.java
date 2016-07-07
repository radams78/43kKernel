import java.util.*;
import java.io.*;

public class BasicRegion extends Region {

	public final static int none = 0,
							isolated = 1,
							top = 2,
							bottom = 3,
							universal = 4,
							bothTopAndBottom = 5;
	
	public final static int[] internalTypes = {0,1,2,3,4,5};
	public final static int[] numVerticesByType = {0,1,1,1,1,2};
	
	public final static String[] typeNames = {"none", "isolated", "top", "bottom", "universal", "top+bottom"};
	
	public final static List<Integer> hasTopVertex = new LinkedList<Integer> (Arrays.asList(top,universal,bothTopAndBottom));
	public final static List<Integer> hasBottomVertex = new LinkedList<Integer> (Arrays.asList(bottom,universal,bothTopAndBottom));
	
	private List<Pair<Integer, Integer> > internalEdges;

	public final int leftInternalType, rightInternalType;
	
	private Signature mySignature;
	public Signature getSignature() {return mySignature;}
	
	private BasicRegionDescriptor desc;
	public RegionDescriptor getDescriptor() {return desc;}
	
	
	private static int computeSize(BoundaryGarden g, int boundaryID, int leftInternalType, int rightInternalType) {
		return g.getBoundary(boundaryID).size + numVerticesByType[leftInternalType] + numVerticesByType[rightInternalType]; 
	}
	
	BasicRegion(BoundaryGarden g, int boundaryID, int leftInternalType, int rightInternalType, boolean hasLeftEdge, boolean hasRightEdge) {
		super(g, boundaryID, computeSize(g, boundaryID, leftInternalType, rightInternalType));
		this.leftInternalType = leftInternalType;
		this.rightInternalType = rightInternalType;

		// Set the descriptor
		this.desc = new BasicRegionDescriptor(g, boundaryID, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge);
		
		internalEdges = new LinkedList<Pair<Integer, Integer> > ();
		if(hasLeftEdge) {
			internalEdges.add(new Pair<Integer, Integer> (myBoundary.topPathVertex(1), myBoundary.bottomPathVertex(1)));			
		}
		
		if(hasRightEdge) {
			internalEdges.add(new Pair<Integer, Integer> (myBoundary.topPathVertex(2), myBoundary.bottomPathVertex(2)));			
		}

		
		setSignature();
	}

	public void setSignature() {
		ArrayList<Integer> sig = new ArrayList<Integer> ();
		for(InputPair inp : myGarden.getAllInputs(boundaryID)) {
			sig.add(computeSignatureAt(inp.first, inp.second));
		}
		mySignature = new Signature(sig);
	}
	
	private int computeSignatureAt(Set<Integer> X, Set<Integer> D) {
		if(dominatesAll(X,D)) return 0;
		
		for(int v : myBoundary.vertexSet()) {
			Set<Integer> bigX = new TreeSet<Integer> (X);
			bigX.add(v);
			if(dominatesAll(bigX, D)) return 1;
		}
		return 2;
	}
	
	private boolean dominatesAll(Set<Integer> X, Set<Integer> D) {
		return dominatesBoundary(X,D) && dominatesInternal(X);
	}
	
	private boolean dominatesBoundary(Set<Integer> X, Set<Integer> D) {
		Set<Integer> NX =  myBoundary.neighbors(X);
		for(Pair<Integer, Integer> edge : internalEdges) {
			if(X.contains(edge.first)) NX.add(edge.second);
			if(X.contains(edge.second)) NX.add(edge.first);
		}
		return NX.containsAll(D);
	}
	
	private boolean dominatesInternal(Set<Integer> X) {return dominatesLeftInternal(X) && dominatesRightInternal(X);}
	
	private boolean dominatesLeftInternal(Set<Integer> X) {
		if(X.contains(myBoundary.topPathVertex(0))) return true;
		
		switch(leftInternalType) {
			case none: return true;
			case isolated: return false;
			case top: return X.contains(myBoundary.topPathVertex(1));
			case bottom: return X.contains(myBoundary.bottomPathVertex(1));
			case universal: return X.contains(myBoundary.topPathVertex(1)) || X.contains(myBoundary.bottomPathVertex(1));
			case bothTopAndBottom: return X.contains(myBoundary.topPathVertex(1)) && X.contains(myBoundary.bottomPathVertex(1));
			default: return false;
		}
		
	}
	
	private boolean dominatesRightInternal(Set<Integer> X) {
		if(X.contains(myBoundary.topPathVertex(myBoundary.topPathLength() + 1))) return true;
		
		switch(rightInternalType) {
			case none: return true;
			case isolated: return false;
			case top: return X.contains(myBoundary.topPathVertex(2));
			case bottom: return X.contains(myBoundary.bottomPathVertex(2));
			case universal: return X.contains(myBoundary.topPathVertex(2)) || X.contains(myBoundary.bottomPathVertex(2));
			case bothTopAndBottom: return X.contains(myBoundary.topPathVertex(2)) && X.contains(myBoundary.bottomPathVertex(2));
			default: return false;
		}
	}

	public boolean equals(Object o) {
		if(!(o instanceof BasicRegion)) return false;
		BasicRegion br = (BasicRegion) o;
		return getDescriptor().equals(br.getDescriptor());
	}

    public void toCoq(String name, PrintWriter writer) {
	String boundaryName = name + "_boundary";
	myBoundary.toCoq(boundaryName, writer);
	writer.println("Definition " + name + " : BasicRegion :=");
	writer.println("  mkBasicRegion " + boundaryName);
	writer.println("  " + typeNames[leftInternalType] + " " + typeNames[rightInternalType]);
	writer.println("  " + desc.hasLeftEdge + " " + desc.hasRightEdge + ".");
    }
}
