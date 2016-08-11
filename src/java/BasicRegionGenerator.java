import java.io.*;
import java.util.*;

// Generates all basic regions with a particular boundary.
public class BasicRegionGenerator extends CoqObject {

    BoundaryGarden myGarden;
    int boundaryId;
    Boundary myBoundary;
    
    boolean topPathIsLong,  bottomPathIsLong, leftSideHasRoom, rightSideHasRoom, canHaveLeftEdge, canHaveRightEdge;

    static final boolean[] truthValues = {true, false};
    
    List<BasicRegion> basicRegions;
    List<BasicRegion> getAllBasicRegions() {return basicRegions;}

    BasicRegionGenerator(BoundaryGarden myGarden, int boundaryId, Boundary myBoundary,
			 boolean topPathIsLong, boolean bottomPathIsLong, boolean leftSideHasRoom, boolean rightSideHasRoom,
			 boolean canHaveLeftEdge, boolean canHaveRightEdge, List<BasicRegion> basicRegions) {
	super(basicRegions, BasicRegion.COQTYPE);
	this.myGarden = myGarden;
	this.boundaryId = boundaryId;
	this.myBoundary = myBoundary;
	this.topPathIsLong = topPathIsLong;
	this.bottomPathIsLong = bottomPathIsLong;
	this.leftSideHasRoom = leftSideHasRoom;
	this.rightSideHasRoom = rightSideHasRoom;
	this.canHaveLeftEdge = canHaveLeftEdge;
	this.canHaveRightEdge = canHaveRightEdge;
	this.basicRegions = basicRegions;
    }

    static BasicRegionGenerator makeBasicRegionGenerator(BoundaryGarden myGarden, int boundaryId) {
	Boundary myBoundary = myGarden.getBoundary(boundaryId);
	
	boolean topPathIsLong = (myBoundary.topPathLength() == Path.PathLength.two);
	boolean bottomPathIsLong = (myBoundary.bottomPathLength() == Path.PathLength.two);
	boolean leftSideHasRoom =  ! myBoundary.topPathVertex(1).equals(myBoundary.bottomPathVertex(1));
	boolean rightSideHasRoom = ! myBoundary.topPathVertex(myBoundary.topPathLength().toInt).equals(myBoundary.bottomPathVertex(myBoundary.bottomPathLength().toInt)); 
	
	boolean canHaveLeftEdge = 		topPathIsLong && bottomPathIsLong 
	    && !myBoundary.areNeighbors(myBoundary.topPathVertex(1), myBoundary.bottomPathVertex(1));
	
	boolean canHaveRightEdge = 		topPathIsLong && bottomPathIsLong 
	    && !myBoundary.areNeighbors(myBoundary.topPathVertex(2), myBoundary.bottomPathVertex(2));

	ArrayList<BasicRegion> basicRegions = new ArrayList<BasicRegion>();
	
	for(InternalType leftInternalType : InternalType.values()) { 
	    for(boolean hasLeftEdge : truthValues) {
		if(verifyTypeAndEdge(leftInternalType, hasLeftEdge, leftSideHasRoom, canHaveLeftEdge, topPathIsLong, bottomPathIsLong)) {		    
		    for(InternalType rightInternalType : InternalType.values()) {
			for(boolean hasRightEdge : truthValues) {
			    if(verifyTypeAndEdge(rightInternalType, hasRightEdge, rightSideHasRoom, canHaveRightEdge, topPathIsLong, bottomPathIsLong)) {
				basicRegions.add(new BasicRegion(myGarden, boundaryId, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge));
			    }
			}
		    }
		}
	    }
	}
	return new BasicRegionGenerator(myGarden, boundaryId, myBoundary, topPathIsLong, bottomPathIsLong, leftSideHasRoom, rightSideHasRoom, canHaveLeftEdge, canHaveRightEdge, basicRegions);
    }
    
    private static boolean verifyTypeAndEdge(InternalType internalType, boolean hasEdge, boolean sideHasRoom, boolean canHaveEdge, boolean topPathIsLong, boolean bottomPathIsLong) {
	// no room --> type = none AND no leftvedge.
	if(!sideHasRoom && (internalType != InternalType.none || hasEdge)) return false;
	
	// if has edge --> can have that edge.
	if(hasEdge && !canHaveEdge) return false;
	
	// if has top vertex --> top path is long
	if(internalType.hasTopVertex && !topPathIsLong) return false;
	
	// if has bottom vertex --> bottom path is long
	if(internalType.hasBottomVertex && !bottomPathIsLong) return false;
	
	return true;
    }
}
