import React from "react";
import { MathJaxContext } from "better-react-mathjax";
import mathJaxSource from "mathjax/es5/tex-svg.js?url";
import { createRoot } from "react-dom/client";
import App from "./App";
import "./styles.css";
createRoot(document.getElementById("root")!).render(
  <React.StrictMode>
    <MathJaxContext
      version={3}
      src={mathJaxSource}
      config={{
        startup: { typeset: false },
        options: { enableMenu: false },
        svg: { fontCache: "local" },
      }}
    >
      <App />
    </MathJaxContext>
  </React.StrictMode>,
);
