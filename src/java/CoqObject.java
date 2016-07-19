public interface CoqObject {
    public String getName();
    public String getType();

    /*
     * Outputs a complete Coq proof script that defines the object
     */
    public String toCoq();
}
