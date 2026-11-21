let cssInjected = false;
export function injectWidgetStyles() {
  if (cssInjected) return;
  cssInjected = true;
  const style = document.createElement('style');
  style.textContent = `
    .spytial-container webcola-cnd-graph {
      display: block;
      width: 100%;
      height: 100%;
    }
    .spytial-container webcola-cnd-graph svg {
      width: 100%;
      height: 100%;
    }
    .spytial-loading {
      padding: 8px;
      color: var(--vscode-descriptionForeground);
    }
    .spytial-error {
      padding: 8px;
      color: var(--vscode-errorForeground);
    }
    .spytial-inspection-note { font-size: 12px; margin: 6px 0; }
    .spytial-counterfactual { min-width: 0; }
    .spytial-counterfactual p { margin: .6em 0; }
    .spytial-conflict-proof pre {
      margin: .3em 0 .7em; padding: .5em .8em; white-space: pre-wrap; overflow-wrap: anywhere;
      border-inline-start: 2px solid var(--vscode-editorWarning-foreground, #b48b26);
      background: var(--vscode-textCodeBlock-background, #8881);
    }
    .spytial-replay-choices { display: flex; flex-wrap: wrap; align-items: center; gap: .4em .7em; }
    .spytial-replay-choices select { max-width: 100%; min-width: 0; }
    .spytial-replay-command { white-space: pre-wrap; overflow-wrap: anywhere; }
    .spytial-explorer { margin: 8px 0; }
    .spytial-explorer-summary { cursor: pointer; margin: 6px 0; }
    .spytial-toolbar { display: flex; gap: 8px; flex-wrap: wrap; align-items: center; }
    .spytial-toolbar strong { overflow-wrap: anywhere; margin-right: auto; }
    .spytial-toolbar button, .spytial-point-select {
      color: var(--vscode-foreground); background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border, #777); border-radius: 4px; padding: 4px 8px;
    }
    .spytial-toolbar button[aria-pressed=true] { outline: 1px solid var(--vscode-focusBorder, #007acc); }
    .spytial-toolbar button:disabled { opacity: .4; }
    .spytial-panes { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 300px), 1fr)); gap: 12px; }
    .spytial-point-header { display: flex; align-items: center; gap: 8px; margin-top: 10px; }
    .spytial-point-select { max-width: 100%; min-width: 0; }
    .spytial-pair-selectors { display: flex; flex-wrap: wrap; gap: 6px 12px; margin: 8px 0; }
    .spytial-pair-selectors label { flex: 1 1 12em; min-width: 0; display: grid; gap: 2px; }
    .spytial-split { height: min(72vh, 680px); display: grid; min-width: 0; }
    .spytial-divider {
      position: relative; cursor: row-resize; touch-action: none; outline-offset: -2px;
    }
    .spytial-divider::after {
      content: ''; display: block; width: 36px; height: 3px; border-radius: 2px;
      margin: 4px auto; background: var(--vscode-descriptionForeground, #888);
    }
    .spytial-divider:hover::after, .spytial-divider:focus-visible::after {
      background: var(--vscode-focusBorder, #087aba);
    }
    .spytial-context-pane { min-height: 0; min-width: 0; display: flex; flex-direction: column; font-size: 12px; }
    .spytial-context-pane header {
      display: flex; flex-wrap: wrap; align-items: center; gap: 3px 8px; padding: 3px 6px;
      border-bottom: 1px solid var(--vscode-panel-border, #8886);
    }
    .spytial-context-pane header span, .spytial-context-pane small { color: var(--vscode-descriptionForeground); }
    .spytial-context-pane header small, .spytial-context-pane header button { margin-inline-start: auto; }
    .spytial-context-scroll { min-height: 0; overflow: auto; overscroll-behavior: contain; scrollbar-gutter: stable; }
    .spytial-context-pane code { white-space: pre-wrap; overflow-wrap: anywhere; }
    .spytial-context-decl { padding: 2px 0; border-bottom: 1px solid var(--vscode-panel-border, #8883); }
    .spytial-context-text, .spytial-context-fact, .spytial-context-decl summary { padding: 3px 6px; }
    .spytial-context-decl summary { cursor: pointer; }
    .spytial-context-decl summary small, .spytial-context-fact small { margin-inline-start: .5em; }
    .spytial-derived { margin: 2px 0 2px 1em; border-inline-start: 1px solid var(--vscode-panel-border, #888); }
    .spytial-context-fact {
      display: block; width: 100%; text-align: start; font: inherit; color: inherit; cursor: pointer;
      border: 0; border-inline-start: 2px solid transparent; background: transparent;
    }
    .spytial-context-fact[data-active=true] { background: var(--vscode-list-hoverBackground, #8882);
      border-inline-start-color: var(--vscode-focusBorder, #087aba); }
    .spytial-context-pane :focus-visible, .spytial-divider:focus-visible {
      outline: 1px solid var(--vscode-focusBorder, #087aba); outline-offset: -1px;
    }
    [data-spytial-compare-side=left] {
      --spytial-difference: var(--vscode-editorGutter-deletedBackground, #c74e39);
      --spytial-difference-line: var(--vscode-diffEditor-removedLineBackground);
      --spytial-difference-active: var(--vscode-diffEditor-removedTextBackground);
    }
    [data-spytial-compare-side=right] {
      --spytial-difference: var(--vscode-editorGutter-addedBackground, #43854a);
      --spytial-difference-line: var(--vscode-diffEditor-insertedLineBackground);
      --spytial-difference-active: var(--vscode-diffEditor-insertedTextBackground);
    }
    .spytial-only-here {
      border-inline-start: 3px solid var(--spytial-difference);
      background-color: var(--spytial-difference-line, color-mix(in srgb, var(--spytial-difference) 14%, transparent));
    }
    .spytial-context-fact.spytial-only-here[data-active=true] {
      border-inline-start-color: var(--spytial-difference);
      background-color: var(--spytial-difference-active, color-mix(in srgb, var(--spytial-difference) 27%, transparent));
    }
    .spytial-context-pane header .spytial-only-here { padding-inline: 4px; color: inherit; }
    .spytial-sr-only { position: absolute; width: 1px; height: 1px; overflow: hidden; clip-path: inset(50%); }
    .spytial-container {
      position: relative;
      overflow: hidden;
      border: 1px solid var(--vscode-panel-border, #333);
      border-radius: 4px;
    }
    .spytial-resize-handle {
      touch-action: none;
      position: absolute;
      bottom: 0;
      right: 0;
      width: 16px;
      height: 16px;
      cursor: nwse-resize;
      opacity: 0.4;
    }
    .spytial-resize-handle:hover {
      opacity: 0.8;
    }
    .spytial-resize-handle::after {
      content: '';
      position: absolute;
      bottom: 3px;
      right: 3px;
      width: 8px;
      height: 8px;
      border-right: 2px solid var(--vscode-foreground);
      border-bottom: 2px solid var(--vscode-foreground);
    }

    /* ErrorMessageModal styles (adapted from spytial-core for VS Code infoview) */
    .spytial-layout-error #error-message-modal {
      border: 2px solid var(--vscode-inputValidation-warningBorder, #cca700);
      border-radius: 8px;
      padding: 12px;
      margin-bottom: 8px;
      background: var(--vscode-inputValidation-warningBackground, #352a05);
      overflow-x: auto;
      font-size: 12px;
    }
    .spytial-layout-error #error-message-modal h4 {
      color: var(--vscode-editorWarning-foreground, #cca700);
      margin: 0 0 6px 0;
      font-size: 13px;
    }
    .spytial-layout-error #error-message-modal p {
      margin: 0 0 8px 0;
      color: var(--vscode-foreground);
    }
    .spytial-layout-error #error-message-modal code {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: 11px;
    }

    /* Constraint relationship table */
    .spytial-layout-error .constraint-relationship-table {
      width: 100%;
      margin-bottom: 8px;
    }
    .spytial-layout-error .constraint-relationship-table table {
      width: 100%;
      border-collapse: collapse;
    }
    .spytial-layout-error .constraint-relationship-table th {
      text-align: left;
      padding: 6px 8px;
      border-bottom: 2px solid var(--vscode-panel-border, #444);
      color: var(--vscode-descriptionForeground);
      font-size: 11px;
      font-weight: 600;
    }
    .spytial-layout-error .constraint-relationship-table td {
      padding: 0;
      vertical-align: top;
      border-bottom: 1px solid var(--vscode-panel-border, #333);
    }
    .spytial-layout-error .constraint-item {
      padding: 6px 8px;
      border-bottom: 1px solid var(--vscode-panel-border, #222);
      transition: background 0.15s;
      cursor: default;
    }
    .spytial-layout-error .constraint-item:last-child {
      border-bottom: none;
    }
    .spytial-layout-error .constraint-item.highlight-source {
      background-color: rgba(255, 193, 7, 0.25);
      border-radius: 3px;
    }
    .spytial-layout-error .constraint-item.highlight-diagram {
      background-color: rgba(255, 193, 7, 0.5);
      border-radius: 3px;
    }

    /* Error card (parse/generic/group errors) */
    .spytial-layout-error .error-card {
      border: 1px solid var(--vscode-panel-border, #444);
      border-radius: 4px;
      overflow: hidden;
    }
    .spytial-layout-error .error-card .card-header {
      padding: 6px 10px;
      background: var(--vscode-editorWidget-background, #252526);
      border-bottom: 1px solid var(--vscode-panel-border, #444);
      font-size: 11px;
    }
    .spytial-layout-error .error-card .card-body {
      padding: 8px 10px;
    }

    /* Selector error list */
    .spytial-layout-error .error-card .list-unstyled {
      list-style: none;
      padding: 0;
      margin: 0;
    }
    .spytial-layout-error .error-card .list-unstyled li {
      padding: 6px 8px;
      margin-bottom: 4px;
      background: var(--vscode-editorWidget-background, #1e1e1e);
      border-radius: 4px;
      font-size: 11px;
    }
    .spytial-layout-error .text-danger {
      color: var(--vscode-errorForeground, #f48771);
    }

    /* Bootstrap utility classes used by ErrorMessageModal */
    .spytial-layout-error .mt-3 { margin-top: 0; }
    .spytial-layout-error .mb-0 { margin-bottom: 0; }
    .spytial-layout-error .mb-2 { margin-bottom: 8px; }
    .spytial-layout-error .p-0 { padding: 0; }
    .spytial-layout-error .p-2 { padding: 8px; }
    .spytial-layout-error .p-3 { padding: 12px; }
    .spytial-layout-error .d-flex { display: flex; }
    .spytial-layout-error .flex-column { flex-direction: column; }
    .spytial-layout-error .h-100 { height: 100%; }
    .spytial-layout-error .bg-light { background: var(--vscode-editorWidget-background, #252526); }
    .spytial-layout-error .rounded { border-radius: 4px; }
    .spytial-layout-error .border { border: 1px solid var(--vscode-panel-border, #444); }
    .spytial-layout-error .border-danger { border-color: var(--vscode-inputValidation-warningBorder, #cca700); }
    .spytial-layout-error .border-2 { border-width: 2px; }
    .spytial-layout-error .table-bordered th, .spytial-layout-error .table-bordered td {
      border: 1px solid var(--vscode-panel-border, #333);
    }
    .spytial-layout-error #hover-instructions {
      font-style: italic;
      font-size: 11px;
      color: var(--vscode-descriptionForeground);
    }
  `;
  document.head.appendChild(style);
}
