public interface CoqObject {
    public String getName();

    /*
     * Outputs a complete Coq proof script that defines the object
     */
    public String toCoq();
}
