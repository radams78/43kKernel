
/*
 * Class that contains a transcript of the data used to create a basic region.
 */
public class BasicRegionDescriptor extends RegionDescriptor {
	private BoundaryGarden myGarden;
	public final int boundaryID, leftInternalType, rightInternalType;
	public final boolean hasLeftEdge, hasRightEdge;
	
	BasicRegionDescriptor(BoundaryGarden g, int boundaryID, int leftInternalType, int rightInternalType, boolean hasLeftEdge, boolean hasRightEdge) {
		this.myGarden = g;
		this.boundaryID = boundaryID;
		this.leftInternalType = leftInternalType;
		this.rightInternalType = rightInternalType;
		this.hasLeftEdge = hasLeftEdge;
		this.hasRightEdge = hasRightEdge;
	}
	
	public String toString() {
		String ans = "<-- " + myGarden.getBoundaryName(boundaryID);
		ans = ans + " | LI: " + BasicRegion.typeNames[leftInternalType] + " | RI: " + BasicRegion.typeNames[rightInternalType];
		ans = ans + " | LE: " + hasLeftEdge + " | RE: " + hasRightEdge + " -->";
		return ans;
	}
	
	public boolean equals(Object o) {
		if(!(o instanceof BasicRegionDescriptor)) return false;
		BasicRegionDescriptor brd = (BasicRegionDescriptor) o;
		return 	brd.isMyGarden(myGarden) && boundaryID == brd.boundaryID && leftInternalType == brd.leftInternalType
				&& rightInternalType == brd.rightInternalType && hasLeftEdge == brd.hasLeftEdge && hasRightEdge == brd.hasRightEdge;
	}
	
	public boolean isMyGarden(BoundaryGarden g) {return myGarden.equals(g);}
	
	 
	
}
