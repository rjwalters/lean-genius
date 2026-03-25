import type { ProofEntry } from "@/types";
import meta from "./meta.json";
import annotations from "./annotations.json";

const entry: ProofEntry = {
  ...meta,
  annotations,
};

export default entry;
