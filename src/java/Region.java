public abstract class Region {

	protected BoundaryGarden myGarden;
	protected Boundary myBoundary;
	
	public final int boundaryID;
	public final int size;
	
	Region(BoundaryGarden g, int ID, int s) {
		myGarden = g;
		boundaryID = ID;
		size = s;
		myBoundary = myGarden.getBoundary(boundaryID);
	}
	
	public abstract Signature getSignature(); 
	
	public abstract RegionDescriptor getDescriptor();

	public String toString() {return getDescriptor().toString();}

	public SignatureTranscript getSignatureTranscript() {
		return new SignatureTranscript(myBoundary, getSignature());
	}

}