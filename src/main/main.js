'use strict';

const path = require('node:path');
const fs = require('node:fs');
const { randomBytes } = require('node:crypto');
const { pathToFileURL } = require('node:url');
const {
  app, BrowserWindow, Tray, ipcMain, screen, protocol, net, shell, globalShortcut, nativeImage,
  clipboard, ClipboardItem, dialog, powerMonitor, desktopCapturer, Menu,
} = require('electron');

const config = require('./config');
const { DISPLAY_NAME } = require('./identity');
const { LANGS } = require('./labels');
const { createSettingsWindow } = require('./settings-window');
const { installChatSpelling } = require('./chat-spelling');
const { overlayPatch } = require('./settings-policy');
const { SettingsAgent } = require('./settings-agent');
const { createBridge } = require('./bridge');
const { startWindowWatch } = require('./windows');
const { startFullscreenWatch } = require('./fullscreen');
const { createTopmostGuard } = require('./topmost-guard');
const { SpeechInput } = require('./speech');
const { SpeechOutput } = require('./tts');
const { CodexBrain } = require('./codex-brain');
const { CodexTools } = require('./codex-tools');
const { ScreenAccess } = require('./screen-access');
const { WindowsAccessibility } = require('./windows-accessibility');
const { desktopHighlight } = require('./desktop-highlight');
const { layoutTarget } = require('./guide-session');
const { GuideTargets } = require('./guide-targets');
const { layoutScene } = require('./guide-scene');
const { createGuideLayer } = require('./guide-layer');
const { GuideSession } = require('./guide-session');
const { WalkthroughController } = require('./walkthrough-controller');
const { ExclusiveFullscreenGate, exclusiveFullscreen } = require('./exclusive-fullscreen');
const { CognitiveFoundation } = require('./cognitive-foundation');
const { GroundedCuriosity } = require('./grounded-curiosity');
const { ReflectionEngine } = require('./cognitive-reflection');
const { ProactiveConversation, BUSY_PAUSE } = require('./proactive-conversation');
const { InitiativeTrial } = require('./initiative-trial');
const { CompanionInterests } = require('./companion-interests');
const { InterestCollaboration } = require('./interest-collaboration');
const { CompanionGoals } = require('./companion-goals');
const { personalityContext } = require('./personality');
const { CodexEvents } = require('./codex-events');
const { connectionFile } = require('../../hooks/stella-codex-hook');
const codexEvents = new CodexEvents();
let integrationToken;
const apps = require('./apps');
const { MemoryStore } = require('./memory');
const { RecentConversation } = require('./recent-conversation');
const { statements, topicKey, mentionsTopic, topicRequest } = require('./personal-context');
const { ContextService, permissions } = require('./pc-context');
const { PersonalAssistant } = require('./personal-assistant');
const { MemoryAgent } = require('./memory-agent');
const { Agent } = require('./agent');
const { ForegroundPriority } = require('./foreground-priority');
const { ActionAgent } = require('./action-agent');
const { WebTools, publicUrl } = require('./web-tools');
const { createLinkOpener } = require('./link-open');
const { DesktopTools } = require('./desktop-tools');
const { MusicPlayback } = require('./music-playback');
const { observePlayback, observeWorkspace } = require('./windows-action-observer');
const { RequestInterpreter } = require('./request-interpreter');
const { createAgentBrowser } = require('./agent-browser');
const { WorldState } = require('./world-state');
const capabilities = require('./capabilities');
const { ReminderStore } = require('./reminders');
const { ReminderScheduler } = require('./reminder-scheduler');
const { ReminderController } = require('./reminder-controller');
const { routeReminderCommand } = require('./reminder-commands');
const { reminderRows, moveReminder } = require('./reminder-settings');
// Reminders (reminder-controller.js): created after app ready; card actions and voice replies go through `reminders`.
let reminderStore = null, reminderScheduler = null, reminders = null;
let memoryStore, recentChatStore, goalStore, autonomy, reflection, curiosity, interests;
let sessionAvailable = true;
let checkInDeadline = 0;
let projectRouting = false;
let projectFeedbackAnchor = null;
// A spoken wake address temporarily permits requested foreground work, not background actions.
let voiceSession = false;
const agentConfig = () => voiceSession ? { ...config.load(), gamingMode: false } : config.load();
let presentation = personalityContext();
const bodyJobs = new Map();
const memory = () => {
  if (!memoryStore) memoryStore = new MemoryStore(path.join(app.getPath('userData'), 'personal-memory.sqlite'), {
    retentionDays: () => permissions(config.load().privacy).retentionDays,
  });
  return memoryStore;
};
function recentConversation(create = false) {
  if (!recentChatStore) {
    const file = path.join(app.getPath('userData'), 'recent-conversation.sqlite');
    if (create || fs.existsSync(file)) recentChatStore = new RecentConversation(file);
  }
  return recentChatStore;
}
function quietTopics() {
  const p = permissions(config.load().privacy);
  return p.memoryEnabled && p.memoryRecall ? memory().quietTopics() : [];
}
function canBringUp(text) {
  return !quietTopics().some(({ key }) => mentionsTopic(text, key));
}

async function routeTopicPreference(text) {
  const p = permissions(config.load().privacy);
  const list = /^\/memory\s+topics$/i.test(text.trim());
  const reply = text => ({ handled: true, text });
  if (/^(?:\/memory\s+recaps|(?:show|list) (?:me )?my (?:saved )?topic recaps)[.!]?$/i.test(text.trim())) {
    const recaps = memory().recaps.list();
    return reply(recaps.length ? recaps.map(row =>
      [row.topic, row.point, row.progress && `Progress: ${row.progress}`, row.spoiler_limit && `Spoiler limit: ${row.spoiler_limit}`]
        .filter(Boolean).join('\n')).join('\n\n') : 'No topic recaps saved.');
  }
  const forgetRecap = /^forget (?:(?:the|our) )?(?:recap (?:for|about|on|of) (.{2,100})|(.{2,100}) recap)[.!]?$/i
    .exec(text.trim().replace(/[.!]+$/, ''));
  if (forgetRecap) {
    if (brain.busy) return reply('Finish the current reply before changing what I remember.');
    const topic = forgetRecap[1] || forgetRecap[2];
    const recaps = memory().recaps;
    if (!recaps.get(topic)) return reply(`I don’t have a saved recap for “${topic}”.`);
    if (p.memoryConfirmChanges && !await confirmMemory('Forget this recap?', `Remove the saved topic recap for “${topic}”.`)) {
      return reply('I’ve kept it.');
    }
    recaps.forget(topic);
    return reply(`I’ve removed the saved recap for “${topic}”.`);
  }
  if (list) {
    const topics = memory().quietTopics();
    return reply(topics.length ? topics.map(row => row.topic).join('\n') : 'There are no topics set aside.');
  }
  const request = topicRequest(text);
  if (!request || config.load().gamingMode) return null;
  let { topic } = request;
  if (/^(?:that|this|that topic|this topic|ese tema|este tema)$/i.test(topic)) {
    const last = (brain.history.length ? brain.history : recentConversation()?.read() || [])
      .findLast(row => row.role === 'user');
    const details = last ? statements(last.content) : [];
    if (request.action !== 'forget' || details.length !== 1) return reply(
      request.action === 'forget' ? 'Which detail do you want me to forget?' : 'Which topic should I bring up less?');
    topic = details[0];
  }
  const key = topicKey(topic.replace(/^that\s+/i, ''));
  if (request.action !== 'forget') {
    if (!p.memoryEnabled) return reply('Turn on Personal memory in the Control room to save topic preferences.');
    const quiet = request.action === 'less';
    const changed = memory().setQuiet(topic, quiet);
    return reply(quiet ? `I’ll leave “${topic}” for you to bring up.`
      : changed ? `I can bring up “${topic}” again.` : `“${topic}” was already available to bring up.`);
  }
  if (/^(?:memory\s+)?#?\d+$/i.test(topic) || /^(?:everything|all|all my memories)$/i.test(topic)) return null;
  if (brain.busy) return reply('Finish the current reply before changing what I remember.');
  const store = memory();
  const rows = store.matchingTopic(key);
  // Compound and explicitly curated entries need the existing memory editor.
  if (rows.some(row => row.source !== 'conversation-stated' ||
      (topicKey(row.text) !== key && /\b(?:and|or|y|o)\b|[,;]/i.test(row.text)))) return null;
  const history = config.load().rememberRecentChat === true ? recentConversation() : undefined;
  const inHistory = [...brain.history, ...(history?.read() || [])].some(row => mentionsTopic(row.content, key));
  const hasRecap = Boolean(store.recaps.get(topic));
  if (!rows.length && !inHistory && !hasRecap) return null;
  if (p.memoryConfirmChanges && !await confirmMemory('Forget this topic?', `Remove saved memories and recent chat exchanges about “${topic}”.`)) {
    return reply('I’ve kept it.');
  }
  const removedChats = history?.forgetTopic(key) || 0;
  if (rows.length) store.applyChanges(rows.map(row => ({ kind: 'forget', id: row.id })), rows);
  const removedRecap = hasRecap && store.recaps.forget(topic);
  brain.reset({ keepRecent: true });
  if (rows.length || removedChats || inHistory || removedRecap) return reply(`I’ve cleared what I was keeping about “${topic}”.`);
  return null;
}
const pcContext = new ContextService({ settings: () => config.load() });
const goals = () => {
  if (!goalStore) goalStore = new CompanionGoals({
    file: path.join(app.getPath('userData'), 'companion-goals.sqlite'), settings: () => config.load(),
    choose: async () => {
      const result = await dialog.showOpenDialog({ title: 'Choose Stella’s project folder', properties: ['openDirectory'] });
      return result.canceled ? null : result.filePaths[0];
    },
    confirm: confirmMemory,
  });
  return goalStore;
};
const world = new WorldState({ context: pcContext });
const closeApp = require('./action-confirmation').createCloseHandler({ config, apps, dialog });
const { deliveryStyle } = require('./voice-delivery');
async function closeRequestedApp({ name, force }, check) {
  if (!config.load().desktopActions || config.load().gamingMode) throw Error('Desktop actions are paused.');
  const key = value => String(value || '').trim().toLowerCase().replace(/\.exe$/, '');
  const target = key(name);
  const matches = (await apps.list()).filter(row => [row.name, row.process, row.label].some(value => key(value) === target));
  check();
  if (matches.length !== 1) return { completed: false, reason: matches.length ? 'More than one running app matches.' : 'No closeable running app matches that name.' };
  const result = await closeApp(null, { name: matches[0].process, force }, check);
  return { ...result, completed: !result.error && result.running === false, app: matches[0].label || matches[0].name };
}
const foreground = new ForegroundPriority(() => ({
  get busy() { return agent.busy || Boolean(autonomy?.busy) || Boolean(reflection?.busy); },
  get reason() { return agent.busy ? agent.reason : 'autonomous'; },
  get done() { return Promise.allSettled([agent.done, autonomy?.done, reflection?.done]); },
  cancel() { agent.cancel(); autonomy?.cancel(); reflection?.cancel(); },
}));
// Legacy structured decision services use the same Codex transport, never Ollama.
// agentConfig: a voice session lifts Gaming mode, so a voice-started walkthrough can still re-plan (spec §8, decision 2).
const decisionBrain = new CodexBrain({ settings: agentConfig,
  cwd: path.join(app.getPath('temp'), 'stella-codex-decisions'),
  tools: { specs: () => [], instructions: () => 'Return only the JSON decision requested in the supplied schema. No tools or actions.' } });
const inferDecision = async (request, signal) => {
  const stop = () => decisionBrain.cancel();
  signal?.throwIfAborted(); signal?.addEventListener('abort', stop, { once: true });
  try {
    decisionBrain.reset();
    return await decisionBrain.chat(JSON.stringify({ schema: request.schema, messages: request.messages }));
  } finally { signal?.removeEventListener('abort', stop); decisionBrain.reset(); }
};
const decisionModels = async () => ['codex'];
const agent = new Agent({ model: 'codex',
  settings: () => config.load(), world, models: decisionModels, apps, close: closeApp,
  infer: inferDecision,
  idle: () => !chats.size && !actions.busy && !memoryRequests.busy && !requests.busy,
  foregroundBusy: () => foreground.active > 0,
  recall: query => {
    const p = permissions(config.load().privacy);
    return p.memoryEnabled && p.memoryRecall ? memory().search(query, 2) : [];
  },
  audit: (kind, status) => { try { memory().audit(kind, status); } catch { console.error('[stella] Agent journal unavailable.'); } },
  notify: text => overlay?.webContents.send('agent:suggestion', text),
});
const desktop = new DesktopTools({ openPath: file => shell.openPath(file), openExternal: url => shell.openExternal(url),
  native: require('./native-windows'), observeWorkspace, preferredBrowser: () => config.load().preferredBrowser });
const agentBrowser = createAgentBrowser({ openUrl: (...args) => desktop.openUrl(...args) });
const actions = new ActionAgent({ settings: () => config.load(), models: decisionModels,
  infer: inferDecision, web: new WebTools(),
  desktop, music: new MusicPlayback({ desktop, observe: observePlayback }), workspace: () => goals().projects.workspace(),
  browser: agentBrowser, idle: () => !chats.size && !agent.busy && !memoryRequests.busy,
  progress: event => overlay?.webContents.send('task:progress', event),
});
const requests = new RequestInterpreter({ actions, settings: () => config.load(), models: decisionModels,
  infer: inferDecision,
  progress: event => overlay?.webContents.send('task:progress', event),
});
const settingsRequests = new SettingsAgent({ localOnly: true, state: settingsState, patch: updateConfig,
  action: settingsAction, open: openSettings,
  infer: inferDecision,
});
const confirmMemory = async (message, detail) => (await dialog.showMessageBox({ type: 'question',
  title: 'Stella — Personal memory', message, detail, buttons: ['Cancel', 'Confirm'],
  defaultId: 0, cancelId: 0, noLink: true })).response === 1;
const memoryRequests = new MemoryAgent({settings: () => config.load(), store: memory,
  models: decisionModels, infer: inferDecision,
  confirm: confirmMemory, idle: () => !chats.size && !agent.busy && !actions.busy,
});
const personal = new PersonalAssistant({
  settings: () => config.load(), store: memory, context: pcContext,
  confirm: confirmMemory,
  exportFile: async (text) => {
    const result = await dialog.showSaveDialog({ title: 'Export personal memories (plain text JSON)',
      defaultPath: 'stella-memories.json', filters: [{ name: 'JSON', extensions: ['json'] }] });
    if (result.canceled || !result.filePath) return false;
    fs.writeFileSync(result.filePath, text, { mode: 0o600 }); return true;
  },
});

async function captureDisplay(displayId, thumbnailSize = { width: 1600, height: 1000 }) {
  const sources = await desktopCapturer.getSources({ types: ['screen'], thumbnailSize, fetchWindowIcons: false });
  const source = sources.find(row => row.display_id === String(displayId));
  if (!source || source.thumbnail.isEmpty()) throw Error('Windows did not provide a screen image.');
  return source.thumbnail;
}

// Gaming mode pauses screen reads, lifted for the user's voice request (agentConfig) and, for guide reads only
// ({ lifted: true } from GuideTargets / a walkthrough re-plan), for a guide or walkthrough the user started: it keeps
// working after the voice session ends, until it finishes, is stopped, or Gaming mode is turned on (which stops it).
// Effects (stella_control, desktop input) are never lifted.
const guideReadLift = () => Boolean(voiceSession || walkthroughs?.active || guide?.active);
const screenAccess = new ScreenAccess({ settings: agentConfig, readLift: guideReadLift,
  displays: () => {
    const fg = require('./native-windows').foregroundBounds();
    const active = fg ? screen.getDisplayNearestPoint(screen.screenToDipPoint({ x: Math.round(fg.x + fg.width / 2), y: Math.round(fg.y + fg.height / 2) })).id : screen.getPrimaryDisplay().id;
    return screen.getAllDisplays().map(d => ({ id: d.id, bounds: d.bounds, primary: d.id === screen.getPrimaryDisplay().id, active: d.id === active }));
  },
  foreground: () => require('./native-windows').foregroundBounds(),
  toNativePoint: point => screen.dipToScreenPoint(point), input: require('./desktop-input').perform,
  confirm: confirmMemory,
  capture: async display => {
    const image = await captureDisplay(display.id);
    return { url: `data:image/jpeg;base64,${image.toJPEG(65).toString('base64')}`, ...image.getSize() };
  },
});
const externalForeground = () => {
  const window = require('./native-windows').foregroundBounds();
  return window?.pid === process.pid ? null : window;
};
// Hand focus back to the app behind her overlay before reading or drawing on it.
const yieldOverlayFocus = async () => {
  if (!overlay?.isFocused()) return;
  overlay.blur();
  await new Promise(resolve => setTimeout(resolve, 100));
};
const highlight = desktopHighlight({ BrowserWindow, screen, foreground: externalForeground,
  enabled: () => screenAccess.enabled() && config.load().visible !== false,
  onError: () => console.error('[stella] Could not keep the desktop highlight visible.'),
  // stella_point: she glides beside the outlined control and points at it until it expires (a walkthrough owns her focus).
  onFocus: focus => { if (!walkthroughs?.active) sendGuideFocus(focus); } });
const accessibility = process.platform === 'win32' ? new WindowsAccessibility({
  settings: () => config.load(), foreground: externalForeground,
  highlight: (bounds, window, check, label) => highlight.show(bounds, window, check, label, { focus: true }), readLift: guideReadLift,
  yieldFocus: yieldOverlayFocus,
  confirm: async (message, detail) => (await dialog.showMessageBox({ type: 'question', title: 'Stella - Desktop action', message,
    detail, buttons: ['Cancel', 'Confirm'], defaultId: 0, cancelId: 0, noLink: true })).response === 1,
  captureWindow: async ({ x, y, width, height }) => {
    const display = screen.getDisplayMatching(screen.screenToDipRect(null, { x, y, width, height }));
    const area = screen.dipToScreenRect(null, display.bounds);
    // OCR needs native pixels; the 1600x1000 default blurs small text on larger displays.
    const image = await captureDisplay(display.id, { width: Math.min(8192, area.width), height: Math.min(8192, area.height) });
    const size = image.getSize();
    const scaleX = area.width / size.width, scaleY = area.height / size.height;
    const left = Math.max(0, Math.ceil((x - area.x) / scaleX)), top = Math.max(0, Math.ceil((y - area.y) / scaleY));
    const right = Math.min(size.width, Math.floor((x + width - area.x) / scaleX));
    const bottom = Math.min(size.height, Math.floor((y + height - area.y) / scaleY));
    if (right <= left || bottom <= top) throw Error('The foreground window is outside the captured display.');
    const cropped = image.crop({ x: left, y: top, width: right - left, height: bottom - top });
    return { image: cropped.toJPEG(90).toString('base64'), x: area.x + left * scaleX, y: area.y + top * scaleY, scaleX, scaleY };
  },
}) : null;
app.on('before-quit', highlight.clear);
// The guide layer is separate from her overlay: onFullscreen hides only the overlay, never this layer.
const guideTargets = new GuideTargets({ accessibility, screen: screenAccess, foreground: externalForeground });
// A guide line goes to the overlay's normal TTS path with a one-time voice grant (spoken while she is hidden in a game).
const guideSay = text => { if (overlay && !overlay.isDestroyed()) overlay.webContents.send('guide:say', { text, grant: tts.grant('guide', text) }); };
// Exclusive-fullscreen games: no guide can appear over them, so guides are refused there and she suggests borderless
// window mode once per game session (exclusive-fullscreen.js; the shell's D3D exclusive-mode state, probed only in fullscreen).
const exclusiveGate = new ExclusiveFullscreenGate({ fullscreen: () => fullscreenState.active,
  exclusive: exclusiveFullscreen, speak: guideSay, lang: () => resolveLang(config.load().lang) });
// Her body (stella_body actions on the overlay), shared by Codex's stella_body tool and walkthrough reactions.
function bodyAction(action, { check = () => {}, signal = new AbortController().signal } = {}) {
  return new Promise((resolve, reject) => {
    check(); if (!overlay || overlay.isDestroyed() || config.load().gamingMode) return reject(Error('Stella’s body is unavailable.'));
    const id = randomBytes(12).toString('hex');
    const finish = (error, result) => { clearTimeout(timer); signal.removeEventListener('abort', stop); bodyJobs.delete(id); error ? reject(error) : resolve(result); };
    const stop = () => finish(Error('Body action cancelled.'));
    const timer = setTimeout(() => finish(Error('Body action timed out.')), 10000);
    bodyJobs.set(id, result => finish(null, result)); signal.addEventListener('abort', stop, { once: true });
    overlay.webContents.send('companion:body', { id, action });
  });
}
const guideLayer = createGuideLayer({ BrowserWindow, screen, preload: path.join(__dirname, '..', 'guide-preload.js'),
  page: path.join(__dirname, '..', 'renderer', 'guide.html') });
const guide = new GuideSession({
  targets: guideTargets, layer: guideLayer,
  layout: scene => layoutScene(scene, { displays: screen.getAllDisplays(), screenToDip: rect => screen.screenToDipRect(null, rect) }),
  // Raw foreground: her own windows (pid) keep the drawing instead of clearing it.
  foreground: () => require('./native-windows').foregroundBounds(), ownPid: process.pid, yieldFocus: yieldOverlayFocus,
  // ScreenAccess reads agentConfig, which lifts Gaming mode only while a voice session is active.
  allowed: () => screenAccess.enabled(), gate: exclusiveGate,
  // A drawing already shown is not cleared when the voice session that asked for it ends (Gaming mode on clears it).
  keep: () => config.load().screenAwareness !== false,
  // stella_draw: her trail of dots runs toward what was drawn (she doesn't move for a drawing).
  onDrawn: laid => sendStellaDraw(layoutTarget(laid, screen.getAllDisplays())),
});
// One walkthrough at a time (walkthrough-controller.js). Re-plans use the decision brain with one fresh screenshot,
// outside chat history. Each line goes to the overlay's normal TTS path with a one-time voice grant, so it is spoken while
// she is hidden in a fullscreen game or Gaming mode (never when voice is off or muted). Commands-only listening follows it.
// Her body comes over on each new step and shows her mood at the end, only while her overlay is visible and not fullscreen.
const walkthroughs = new WalkthroughController({ targets: guideTargets, layer: guideLayer, guide, ownPid: process.pid,
  displays: () => screen.getAllDisplays(), screenToDip: rect => screen.screenToDipRect(null, rect),
  dipToScreen: rect => screen.dipToScreenRect(null, rect), cursor: () => screen.getCursorScreenPoint(),
  foreground: () => require('./native-windows').foregroundBounds(), pointer: () => require('./native-windows').pointerState(),
  processRows: () => require('./native-windows').processRows(), allowed: () => screenAccess.enabled(),
  lang: () => resolveLang(config.load().lang), busy: () => brain.busy || decisionBrain.busy,
  speak: guideSay, onActive: () => syncCommands(), gate: exclusiveGate, reminderWindow: () => Boolean(reminders?.windowOpen()),
  body: action => bodyAction(action), focus: sendGuideFocus,
  bodyAllowed: () => Boolean(overlay && !overlay.isDestroyed() && overlay.isVisible() && !fullscreenState.active && !config.load().gamingMode),
  snapshot: () => screenAccess.snapshot('', () => {}, { lifted: true }),
  infer: async request => {
    decisionBrain.reset();
    try { return await decisionBrain.chat(JSON.stringify(request.messages), () => {}, () => {}, { outputSchema: request.schema, recordHistory: false, images: request.images }); }
    finally { decisionBrain.reset(); }
  } });
guideLayer.onCardAction((displayId, id) => walkthroughs.cardAction(displayId, id));
app.on('before-quit', () => { walkthroughs.stop(); guide.clear('quit'); });
const currentContext = text => {
  const p = permissions(agentConfig().privacy);
  const savedContinuity = goals().continuity.context();
  const remaining = Math.max(0, p.promptBudget - Buffer.byteLength(JSON.stringify(savedContinuity)));
  const savedGoals = p.memoryEnabled && !savedContinuity.length ? goals().context() : [];
  let personalMemory;
  if (p.memoryEnabled && p.memoryRecall) {
    try { personalMemory = memory().personalContext(text); }
    catch { console.error('[stella] Personal memory unavailable.'); }
  }
  return { presentation, capabilities: capabilities.registry(agentConfig()), externalCodexEvents: codexEvents.snapshot(),
  savedContinuity, savedGoals, currentProject: goals().projects.context(Math.max(0, remaining - Buffer.byteLength(JSON.stringify(savedGoals)))),
  companionInterests: interests?.context() || [],
  ...(personalMemory ? { personalMemory } : {}),
  recentTasks: actions.grounding({ includeApps: false }) };
};
const brainTools = new CodexTools({ settings: agentConfig, resolveLanguage: resolveLang, context: pcContext,
  screen: screenAccess, accessibility, guide, walkthroughs, highlight: process.platform === 'win32' ? highlight.show : null, closeApp: closeRequestedApp,
  body: bodyAction, activity: event => sendAgentActivity(event),
  actions, store: memory, goals, curiosity: () => curiosity, state: settingsState, patch: updateConfig, confirm: confirmMemory });
// Stella animates what her agent does: Stella's tools (above) and the AI's own built-in ones (below).
function sendAgentActivity(event) { if (overlay && !overlay.isDestroyed()) overlay.webContents.send('agent:activity', event); }
const brain = new CodexBrain({ settings: agentConfig, recentConversation, activity: sendAgentActivity,
  warmIdleMs: 3 * 60 * 1000, canKeepWarm: () => !config.load().gamingMode && sessionAvailable,
  cwd: path.join(app.getPath('temp'), 'stella-codex-brain'), tools: brainTools,
  systemTools: () => config.load().systemAccess === true, workspace: () => goals().projects.workspace() || app.getPath('home'), context: currentContext,
  onOutcome: receipt => {
    const saved = goals().projects.recordVerification(receipt);
    if (saved) {
      projectFeedbackAnchor = { scope: goals().projects.scope(), at: Date.now() };
      groundedCuriosity.sync(); reflection.schedule();
    }
    return saved;
  },
  approve: async (message, { text, signal, item }) => {
    signal.throwIfAborted();
    const p = message.params;
    return confirmMemory('Review Codex action', JSON.stringify({ currentRequest: text, action: message.method,
      reason: p.reason, command: p.command, cwd: p.cwd, permissions: p.permissions, grantRoot: p.grantRoot, routine: brainTools.routineSession ? { name: brainTools.routineSession.row.name, version: brainTools.routineSession.row.version, step: brainTools.routineSession.index + 1, instruction: brainTools.routineSession.step() } : null, item: item || p.itemId }, null, 2).slice(0, 12000));
  },
});

const { migrateProfile } = require('./profile-migration');
const ROOT = path.resolve(__dirname, '..', '..');
const VERSION = require('../../package.json').version;
const runtime = require('./runtime-info').runtimeInfo(ROOT, VERSION);
const DEV = process.argv.includes('--dev');
app.setName('Stella');
// Her saved data lives in %APPDATA%\Stella; the first start after the rename moves it over from
// her old profile folder (kept as a backup). Smoke tests use their own throwaway profile.
const smokeTest = process.argv.some((arg) => path.basename(arg) === 'smoke-electron.js');
app.setPath('userData', smokeTest && process.env.STELLA_TEST_PROFILE ? process.env.STELLA_TEST_PROFILE
  : migrateProfile(path.join(app.getPath('appData'), 'CapriGPT'), path.join(app.getPath('appData'), 'Stella')).dir);
// Installed Codex transport with no background tools, actions or conversation history.
const cognitiveBrain = new CodexBrain({ settings: () => config.load(),
  cwd: path.join(app.getPath('temp'), 'stella-codex-cognition'),
  tools: { specs: () => [], instructions: () => 'Return only the requested JSON. No tools or actions.' } });
const inferCognitive = async (request, signal) => {
  const stop = () => cognitiveBrain.cancel();
  signal?.throwIfAborted(); signal?.addEventListener('abort', stop, { once: true });
  try {
    cognitiveBrain.reset();
    return await cognitiveBrain.chat(JSON.stringify(request.messages), () => {}, () => {},
      { outputSchema: request.schema, recordHistory: false });
  } finally { signal?.removeEventListener('abort', stop); cognitiveBrain.reset(); }
};
curiosity = new CognitiveFoundation({ file: path.join(app.getPath('userData'), 'curiosity.sqlite'),
  settings: () => config.load(), context: pcContext });
const initiativeTrial = new InitiativeTrial(curiosity.db);
interests = new CompanionInterests({ db: curiosity.db, settings: () => config.load() });
const interestCollaboration = new InterestCollaboration({ interests, infer: inferCognitive, settings: rendererConfig });
const groundedCuriosity = new GroundedCuriosity({ journal: curiosity, goals, settings: () => config.load() });
const cognitiveIdle = () => !foreground.active && !chats.size && !brain.busy && !agent.busy &&
  !actions.busy && !memoryRequests.busy && !requests.busy && !settingsRequests.busy;
function checkInBlock() {
  if (!sessionAvailable) return 'The Windows session was unavailable.';
  if (fullscreenState.active) return 'A fullscreen window was active.';
  if (voiceSession || (speech.current && speech.current.mode !== 'wake') || presentation.chatOpen) {
    return 'A voice or text conversation was active.';
  }
  if (!cognitiveIdle() || reflection.busy || presentation.canSpeak === false) return 'Stella was busy.';
  if (!overlay || overlay.isDestroyed() || !overlay.isVisible()) return 'The overlay was unavailable.';
  if (powerMonitor.getSystemIdleTime() >= 300) return 'The PC was idle.';
  return '';
}
reflection = new ReflectionEngine({ journal: curiosity, settings: () => config.load(),
  model: 'codex', models: decisionModels, infer: inferCognitive,
  canRun: () => cognitiveIdle() && !autonomy?.busy && sessionAvailable && !voiceSession &&
    (!speech.current || speech.current.mode === 'wake') && !fullscreenState.active });
autonomy = new ProactiveConversation({ settings: rendererConfig, journal: curiosity,
  interests, trial: initiativeTrial, canBringUp, quietTopics: () => quietTopics().slice(0, 12).map(row => row.topic),
  model: 'codex', models: decisionModels, infer: inferCognitive,
  observe: () => pcContext.snapshot('companion-conversation', ['contextForeground']),
  warmVoice: () => tts.warm(),
  memories: () => memory().list(10),
  sharedContext: () => {
    const p = permissions(config.load().privacy);
    const project = goals().projects.selected();
    const preferences = p.memoryEnabled && p.memoryRecall ? memory().list(20)
      .filter(row => canBringUp(row.text) && /^(?:I (?:like|love|enjoy|prefer) |me gusta[n]? |prefiero )/i.test(row.text) &&
        !/\b(password|token|address|medical|health|bank|salary|contraseña|salud|banco)\b/i.test(row.text))
      .slice(0, 2).map(row => row.text.slice(0, 140)) : [];
    const name = project && project.name !== project.root ? project.name.slice(0, 100) : '';
    return name || preferences.length ? { project: name, preferences } : null;
  },
  canRun: () => !checkInBlock(), blockedReason: checkInBlock,
  notify: (text, { voiceUntil, mood, replyTo, canBuild } = {}) => {
    if (!overlay || overlay.isDestroyed() || presentation.chatOpen || fullscreenState.active) return false;
    brain.history = [...brain.history, { role: 'assistant', content: text }].slice(-24);
    checkInDeadline = voiceUntil || 0;
    overlay.webContents.send('companion:conversation', { text, voiceUntil, mood, replyTo, canBuild }); return true;
  },
});
const PORT = Number(process.env.STELLA_PORT) || 47823;
const SOUND_EXT = /\.(mp3|wav|ogg|m4a)$/i;

protocol.registerSchemesAsPrivileged([
  { scheme: 'stella', privileges: { standard: true, secure: true, supportFetchAPI: true, stream: true } },
]);

let overlay = null;
let tray = null;
let settingsRoom = null;
let windowWatch = null;
let fullscreenWatch = null;
let fullscreenState = { active: false, revision: 0 };
let fullscreenHideTimer;
// the watcher only speaks when something changes: the overlay asks for this when it (re)loads
let lastWindows = null;
const chats = new Map(); // id -> AbortController of an answer being streamed
const wakeAllowed = () => Boolean(overlay && !overlay.isDestroyed() && config.load().wakeWordEnabled === true
  && (!smokeTest || process.argv.includes('--wake-live')));
// Commands-only listening (spec decision 1): open while a walkthrough runs or a reminder's command window is open,
// in fullscreen and Gaming mode too. Only the fixed local commands are acted on; speech.js drops every other transcript.
// speech.commandsReady() adds the user's voice opt-in (wake word on) and an already installed runtime: never a download.
let commandWindowUntil = 0, commandWindowTimer = null, commandsOn = false, commandsListeningId = null;
const commandsAllowed = () => Boolean(sessionAvailable && overlay && !overlay.isDestroyed()
  && (walkthroughs.active || Date.now() < commandWindowUntil));
// For the reminders plan: open the window for ms (30 s after a reminder fires or is shown).
function openCommandWindow(ms) {
  if (!Number.isFinite(ms) || ms <= 0) return;
  commandWindowUntil = Math.max(commandWindowUntil, Date.now() + Math.min(ms, 120000));
  clearTimeout(commandWindowTimer);
  commandWindowTimer = setTimeout(() => syncCommands(), commandWindowUntil - Date.now() + 50);
  commandWindowTimer.unref?.();
  syncCommands();
}
function syncCommands(force = false) {
  const on = speech.commandsReady();
  if (!on && speech.current?.mode === 'commands') speech.cancel();
  if (on === commandsOn && !force) return;
  commandsOn = on;
  if (!overlay || overlay.isDestroyed()) return;
  // Hidden for a fullscreen game, the overlay must keep capturing while the window is open.
  if (on) overlay.webContents.setBackgroundThrottling(false);
  else if (!overlay.isVisible()) overlay.webContents.setBackgroundThrottling(!config.load().wakeWordEnabled && !voiceSession);
  overlay.webContents.send('speech:commands', { on });
}
function routeSpeechCommand({ command, minutes }) {
  // 'done' / 'snooze': the most recently shown reminder card, within its window; otherwise "done" is a walkthrough's Next.
  walkthroughs.voiceCommand(command, () => Boolean(reminders?.voice({ command, minutes })));
}
const speech = new SpeechInput({
  // Listen in her conversation language (control room → App → Language; 'Follow Windows' resolves it).
  language: () => resolveLang(config.load().lang),
  runtimeDir: app.isPackaged ? path.join(app.getPath('userData'),'speech-runtime') : path.join(ROOT,'.stella-local','speech-runtime'),
  allowed: () => Boolean(overlay && !overlay.isDestroyed() && (voiceSession || (overlay.isVisible()
    && !config.load().gamingMode && !fullscreenState.active))),
  wakeAllowed,
  commandsAllowed,
  wakeEnabled: () => config.load().wakeWordEnabled === true,
  notify: state => {
    if (state.type === 'command') { routeSpeechCommand(state); return; } // handled here, never forwarded
    // The walkthrough card's mic badge follows the commands microphone (her overlay may be hidden in a game).
    if (state.type === 'ready' && state.mode === 'commands') { commandsListeningId = state.id; walkthroughs.setListening(true); }
    // 'wake': the wake address was heard in commands mode, so that stream is now the user's request.
    else if (['stopped', 'wake'].includes(state.type) && state.id === commandsListeningId) { commandsListeningId = null; walkthroughs.setListening(false); }
    if (!overlay || overlay.isDestroyed()) return;
    if (state.type === 'wake' || (state.type === 'ready' && state.mode === 'conversation')) {
      voiceSession = true; autonomy.cancel(); tts.cancel(); tts.warm();
      clearTimeout(fullscreenHideTimer);
      overlay.webContents.setBackgroundThrottling(false); overlay.showInactive();
    }
    overlay.webContents.send('speech:state', state);
  },
});

const tts = new SpeechOutput({ root: ROOT, config: () => config.load(),
  allowed: () => sessionAvailable && speech.allowed() && (voiceSession || config.load().visible !== false)
    && (!speech.current || ['wake', 'conversation', 'commands'].includes(speech.current.mode)),
  // A granted guide/reminder line skips only the visibility, fullscreen and Gaming part of allowed().
  grantAllowed: () => Boolean(sessionAvailable && overlay && !overlay.isDestroyed()
    && (!speech.current || ['wake', 'conversation', 'commands'].includes(speech.current.mode))),
  notify: state => { if (overlay && !overlay.isDestroyed()) overlay.webContents.send('tts:state', state); },
});

function endVoiceSession() {
  const ended = voiceSession;
  voiceSession = false;
  if (speech.current?.wakeActivated) speech.cancel();
  // Not already ended (entering fullscreen ends it and lets her fold away before the hide).
  if (ended && overlay && !overlay.isDestroyed() && (fullscreenState.active || config.load().gamingMode)) {
    setOverlayIgnore(true); setOverlayFocusable(false); overlay.hide();
  }
}

const userSoundsDir = () => path.join(app.getPath('userData'), 'sounds');

// stella://app/...        -> files of this repo
// stella://usersounds/... -> the user's own sound overrides
function serveProtocol() {
  protocol.handle('stella', (request) => {
    const url = new URL(request.url);
    const base = url.host === 'usersounds' ? userSoundsDir() : ROOT;
    const target = path.resolve(base, '.' + decodeURIComponent(url.pathname));
    if (target !== base && !target.startsWith(base + path.sep)) {
      return new Response('forbidden', { status: 403 });
    }
    return net.fetch(pathToFileURL(target).toString());
  });
}

function targetDisplay() {
  const { displayId } = config.load();
  return screen.getAllDisplays().find((d) => d.id === displayId) || screen.getPrimaryDisplay();
}

// A { displayId, rect } target (absolute DIP) for Stella: a rect in overlay coordinates on her display, else the
// direction of its display, else null.
function overlayTarget(focus) {
  if (!focus) return null;
  const home = targetDisplay(), other = screen.getAllDisplays().find(d => d.id === focus.displayId);
  const r = focus.rect;
  if (focus.displayId === home.id) return { rect: { x: r.x - home.workArea.x, y: r.y - home.workArea.y, w: r.width, h: r.height } };
  if (!other) return null;
  const dx = other.bounds.x + other.bounds.width / 2 - (home.bounds.x + home.bounds.width / 2);
  const dy = other.bounds.y + other.bounds.height / 2 - (home.bounds.y + home.bounds.height / 2);
  return { direction: Math.abs(dx) >= Math.abs(dy) ? (dx < 0 ? 'left' : 'right') : (dy < 0 ? 'up' : 'down') };
}

// Tells Stella where the walkthrough or stella_point target is (null: let go and go back).
function sendGuideFocus(focus) {
  if (!overlay || overlay.isDestroyed()) return;
  overlay.webContents.send('guide:focus', overlayTarget(focus));
}

// Tells Stella where stella_draw drew (null: unknown, her trail runs toward the middle).
function sendStellaDraw(target) {
  if (!overlay || overlay.isDestroyed()) return;
  overlay.webContents.send('stella:draw', overlayTarget(target));
}

// On Windows, Electron's setFocusable() also re-adds the window to the taskbar (when focusable) and
// re-applies its extended styles. She is a click-through overlay: keep her out of the taskbar and
// above other apps after every change.
function setOverlayFocusable(on) {
  if (!overlay || overlay.isDestroyed()) return;
  overlay.setFocusable(on);
  overlay.setSkipTaskbar(true);
  overlay.setAlwaysOnTop(true, 'screen-saver');
}

// Click-through only when it changes: re-applying it rewrites the overlay's native window styles, and Windows
// then resets the cursor of whatever is under her (the control room's hand cursor flickered to an arrow every
// 150 ms while her pointer recovery re-sent the same state). Forgotten on show, in case Windows reset it.
// forward: mouse moves are forwarded to her only while the pointer is near her. Each forwarded move makes her
// window set its own (arrow) cursor over whatever app is under it, so forwarding everywhere made every other
// cursor flicker while moving; away from her, her renderer's cursor polling notices the pointer coming close.
let overlayIgnore = null, overlayForward = true;
function setOverlayIgnore(ignore, forward = overlayForward) {
  if (!overlay || overlay.isDestroyed() || (ignore === overlayIgnore && forward === overlayForward)) return;
  overlayIgnore = ignore; overlayForward = forward;
  overlay.setIgnoreMouseEvents(ignore, ignore ? { forward } : undefined);
}

function fitOverlay() {
  if (!overlay) return;
  const { workArea } = targetDisplay();
  overlay.setBounds(workArea);
  overlay.webContents.send('overlay:resize', { width: workArea.width, height: workArea.height });
}

function createOverlay() {
  overlayIgnore = null; overlayForward = true; // a new window starts with no click-through applied
  const { workArea } = targetDisplay();
  overlay = new BrowserWindow({
    ...workArea,
    transparent: true,
    backgroundColor: '#00000000',
    frame: false,
    resizable: false,
    movable: false,
    minimizable: false,
    maximizable: false,
    fullscreenable: false,
    skipTaskbar: true,
    // showInactive() preserves foreground focus. Keep the window capable of
    // receiving native mouse input; only explicit chat/menu requests focus it.
    focusable: true,
    hasShadow: false,
    alwaysOnTop: true,
    type: process.platform === 'win32' ? 'toolbar' : undefined,
    show: false,
    webPreferences: {
      preload: path.join(__dirname, '..', 'preload.js'),
      contextIsolation: true,
      nodeIntegration: false,
      sandbox: true,
      spellcheck: true,
      backgroundThrottling: true,
      autoplayPolicy: 'no-user-gesture-required',
    },
  });

  installChatSpelling(overlay, Menu);
  // Chat links open through link:open; the overlay itself never navigates.
  overlay.webContents.setWindowOpenHandler(() => ({ action: 'deny' }));
  overlay.webContents.on('will-navigate', e => e.preventDefault());
  overlay.setAlwaysOnTop(true, 'screen-saver');
  setOverlayIgnore(true);
  const microphonePermission = (contents, permission, details={}) =>
    contents === overlay?.webContents && permission === 'media' && Boolean(speech.current)
      && speech.permitted(speech.current) && (!details.mediaTypes || details.mediaTypes.every(type=>type==='audio'))
      && (!details.mediaType || details.mediaType==='audio');
  overlay.webContents.session.setPermissionRequestHandler((contents, permission, callback, details) => callback(microphonePermission(contents,permission,details)));
  overlay.webContents.session.setPermissionCheckHandler((contents, permission, origin, details) => microphonePermission(contents,permission,details));
  overlay.on('show', () => { const ignore = overlayIgnore ?? true; overlayIgnore = null; setOverlayIgnore(ignore); });
  overlay.loadURL('stella://app/src/renderer/index.html');
  // always shown: put away, she's still there, resting in the bottom-left corner
  overlay.once('ready-to-show', () => {
    if (!config.load().gamingMode && !fullscreenState.active) {
      overlay.showInactive(); if (config.load().visible !== false) tts.warm();
    }
  });
  overlay.webContents.on('render-process-gone', (_e, details) => {
    speech.cancel(true); tts.cancel(); endVoiceSession();
    console.error('[stella] renderer gone:', details.reason);
  });
  overlay.webContents.on('did-start-loading', () => { speech.cancel(true); tts.cancel(); endVoiceSession(); reminders?.setReady(false); });
  if (DEV) {
    overlay.webContents.on('console-message', (e) => {
      const { level, message, lineNumber, sourceId } = e;
      console.log(`[renderer:${level}] ${message} (${String(sourceId).split('/').pop()}:${lineNumber})`);
    });
    if (process.env.STELLA_DEVTOOLS) overlay.webContents.openDevTools({ mode: 'detach' });
  }
}

// Reminders: one local SQLite file, one timer. A fired reminder speaks with a one-time 'reminder' voice grant (also while
// she is hidden in a fullscreen game or Gaming mode; never when voice is off or muted) and shows her card, or holds the card
// until fullscreen ends / Gaming mode is off. A shown card opens the 30 s commands window for "done" / "snooze".
function startReminders() {
  try {
    reminderStore = new ReminderStore(path.join(app.getPath('userData'), 'reminders.sqlite'));
    reminders = new ReminderController({ store: reminderStore, lang: () => resolveLang(config.load().lang),
      state: () => { const cfg = config.load(); return { fullscreen: fullscreenState.active, gaming: cfg.gamingMode === true,
        overlayAvailable: Boolean(overlay && !overlay.isDestroyed()), voiceOn: Boolean(cfg.ttsEnabled) && !cfg.muted,
        locked: !sessionAvailable }; },
      send: payload => { if (overlay && !overlay.isDestroyed()) overlay.webContents.send('reminder:due', payload); },
      grant: line => tts.grant('reminder', line), openWindow: openCommandWindow,
      isOverlay: sender => Boolean(overlay && !overlay.isDestroyed() && sender === overlay.webContents) });
    reminderScheduler = new ReminderScheduler({ store: reminderStore, fire: (reminder, info) => reminders.fire(reminder, info) });
    brainTools.reminders = reminderStore;
    reminderScheduler.resume();
    reminders.redeliver(); // occurrences still waiting from before the restart, once, as missed
    // Done / cancelled reminders are kept 30 days; the Control room follows changes made by voice or Codex too.
    const prune = () => { try { reminderStore?.prune(); } catch { /* best effort */ } };
    prune();
    const pruneTimer = setInterval(prune, 24 * 3600000); pruneTimer.unref();
    let roomTimer = null;
    reminderStore.onChange(() => { clearTimeout(roomTimer); roomTimer = setTimeout(() => settingsRoom?.update(), 250); roomTimer.unref?.(); });
  } catch (error) {
    console.error('[stella] Reminders unavailable:', error.message);
    reminderScheduler?.stop(); reminderStore?.close();
    reminderStore = reminderScheduler = reminders = null; brainTools.reminders = undefined;
  }
}

function sendCommand(name, payload = {}) {
  if (config.load().gamingMode) return;
  overlay?.webContents.send('stella:command', { name, ...payload });
}

let gamingTransition = false;
async function gamingAnimation(name) {
  if (!overlay || overlay.isDestroyed() || overlay.webContents.isLoading()) return;
  await new Promise(resolve => {
    const contents = overlay.webContents;
    const finish = () => {
      clearTimeout(timer);
      ipcMain.removeListener('gaming:animation-ready', ready);
      resolve();
    };
    const ready = event => { if (event.sender === contents) finish(); };
    const timer = setTimeout(finish, 1100);
    ipcMain.on('gaming:animation-ready', ready);
    contents.send('stella:command', { name });
  });
}
async function setGamingMode(on) {
  if (gamingTransition) return;
  gamingTransition = true;
  try {
    updateConfig({ gamingMode: on });
    if (on) {
      brain.cancel(); decisionBrain.cancel();
      const pending = [...chats.values()];
      pending.forEach(({ abort }) => abort.abort());
      setOverlayFocusable(false);
      pcContext.lastEvent = null;
      windowWatch?.stop();
      windowWatch = null;
      // Bounded goodbye: a missing renderer or a hidden pet cannot delay the pause.
      if (overlay?.isVisible()) await gamingAnimation('gamingDeparture');
      if (!voiceSession) overlay?.hide();
      // Wait for cancelled requests to finish before sending the unload request.
      await Promise.allSettled(pending.map(({ done }) => done));
      await agent.done;
      await requests.done;
      await actions.done;
      agentBrowser.stop();
    } else {
      await gamingAnimation('gamingPrepareReturn');
      if (!fullscreenState.active) overlay?.showInactive();
      overlay?.webContents.send('stella:command', { name: 'gamingArrival' });
      watchWindows();
      overlay?.webContents.send('integration:state', { ...codexEvents.snapshot(), resumed: true });
    }
  } finally { gamingTransition = false; rebuildTray(); }
}

function watchWindows() {
  if (windowWatch || config.load().gamingMode || !config.load().windowTracking) return;
  windowWatch = startWindowWatch({ overlay, onUpdate: (data) => {
    if (lastWindows && lastWindows.fg !== data.fg) curiosity.foregroundChanged().then(question => {
      if (question) reflection.schedule();
    }).catch(() => {});
    lastWindows = data;
    overlay?.webContents.send('windows:update', data);
  } });
}

function onFullscreen(active) {
  if (active === fullscreenState.active) return;
  const revision = fullscreenState.revision + 1;
  fullscreenState = { active, revision };
  exclusiveGate.onFullscreen(active); // a new game session may hear the borderless suggestion again
  // Going fullscreen ends a conversation that was already open, a "Hey Stella" one too (the video's own audio would
  // otherwise keep it, and her window, alive). "Hey Stella" said in fullscreen still starts one. The hide below folds her.
  if (active) { if (!['wake', 'commands'].includes(speech.current?.mode)) speech.cancel(); voiceSession = false; tts.cancel(); }
  clearTimeout(fullscreenHideTimer);
  if (!overlay || overlay.isDestroyed()) return;
  overlay.webContents.setBackgroundThrottling(false);
  if (active) {
    setOverlayIgnore(true);
    if (!voiceSession) setOverlayFocusable(false);
    // Renderer normally acknowledges in 160 ms. This also handles a frozen renderer.
    fullscreenHideTimer = setTimeout(() => {
      if (!voiceSession && fullscreenState.active && fullscreenState.revision === revision && !overlay?.isDestroyed()) {
        overlay?.hide();
        overlay?.webContents.setBackgroundThrottling(!commandsOn);
      }
    }, 260);
  } else if (!config.load().gamingMode) {
    // setFocusable(false) on departure changes native mouse activation too.
    // Restore it without activating or focusing over the user's foreground app.
    setOverlayFocusable(true);
    setOverlayIgnore(true);
    overlay.showInactive();
  }
  overlay.webContents.send('fullscreen:state', fullscreenState);
  if (!active) reminders?.flush(); // held reminder cards appear once fullscreen ends
}

// Ctrl+Alt+C: she goes off to rest, curled up in the bottom-left corner, or comes back out. Put away she is
// quiet (no check-ins or initiatives: the visible === false gates), but a line she is saying is not cut off.
function toggleVisible(force) {
  const visible = typeof force === 'boolean' ? force : !config.load().visible;
  config.save({ visible });
  sendCommand('stow', { on: !visible });
  rebuildTray();
}

// During the demo, a little fake terminal beside her (window tracking is
// Windows only, so only there). Opened without stealing focus; closing it drops her off it.
let demoWin = null;
const DEMO_TERMINAL = `<body style="margin:0;background:#14101c;color:#8f8aa3;font:13px/1.7 Consolas,monospace;padding:14px 18px">
<div style="color:#b9a4f5">PS C:\\star-notes-api&gt; npm test -- notes</div>
<div>&nbsp;&nbsp;GET /notes</div><div style="color:#b9a4f5">&nbsp;&nbsp;&nbsp;&nbsp;✓ returns 20 items per page</div>
<div style="color:#b9a4f5">&nbsp;&nbsp;&nbsp;&nbsp;✓ paginates with a cursor</div><div style="color:#b9a4f5">&nbsp;&nbsp;&nbsp;&nbsp;✓ rejects a bad cursor</div>
<div>&nbsp;&nbsp;6 passing (212ms)</div><div style="color:#b9a4f5">PS C:\\star-notes-api&gt; _</div></body>`;

function demoWindow(open) {
  demoWin?.destroy();
  demoWin = null;
  if (!open || process.platform !== 'win32') return false;
  const b = overlay.getBounds();
  demoWin = new BrowserWindow({
    x: Math.round(b.x + b.width * 0.5 - 310), y: Math.round(b.y + b.height * 0.42), width: 620, height: 300,
    show: false, alwaysOnTop: true, title: 'star-notes-api — npm test', backgroundColor: '#14101c', autoHideMenuBar: true,
  });
  demoWin.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(DEMO_TERMINAL)}`);
  demoWin.once('ready-to-show', () => demoWin?.showInactive());
  demoWin.on('closed', () => { demoWin = null; });
  return true;
}

// 'auto' -> the first system language Stella speaks, English otherwise.
function resolveLang(setting) {
  if (LANGS.includes(setting)) return setting;
  const preferred = [...app.getPreferredSystemLanguages(), app.getSystemLocale(), app.getLocale()];
  for (const tag of preferred) {
    const base = String(tag || '').toLowerCase().split(/[-_]/)[0];
    if (LANGS.includes(base)) return base;
  }
  return 'en';
}

// What the overlay gets: `lang` is the resolved one, `langSetting` what the user picked.
function rendererConfig() {
  const cfg = config.load();
  return { ...cfg, wakeWordEnabled: smokeTest && !process.argv.includes('--wake-live') ? false : cfg.wakeWordEnabled,
    lang: resolveLang(cfg.lang), langSetting: cfg.lang, displayName: DISPLAY_NAME };
}

function updateConfig(patch) {
  const changes = key => Object.hasOwn(patch, key);
  const oldPrivacy = permissions(config.load().privacy);
  const nextPrivacy = patch.privacy ? permissions({ ...oldPrivacy, ...patch.privacy }) : oldPrivacy;
  const revokedRecall = Object.keys(oldPrivacy).some(key =>
    (key === 'memoryEnabled' || key === 'memoryRecall' || key === 'allApps' || key.startsWith('context')) &&
      oldPrivacy[key] === true && nextPrivacy[key] === false);
  const policyChanged = ['routinesEnabled', 'gamingMode', 'agentEnabled', 'desktopActions', 'privacy', 'systemAccess', 'screenAwareness', 'autonomyEnabled', 'autonomyScreen'].some(changes);
  const backendChanged = ['preferredBrowser', 'crunchyrollProfile', 'codexModel', 'codexExecutable', 'codexEffort'].some(changes);
  if (['routinesEnabled', 'projectCuriosityEnabled', 'dailyReviewEnabled', 'dailyReviewNotify', 'proactiveEnabled', 'proactiveVoice', 'cognitiveEnabled', 'interestsEnabled', 'visible', 'lang'].some(changes)) {
    if (typeof autonomy !== 'undefined') autonomy?.touch();
    if (typeof reflection !== 'undefined') reflection?.cancel();
  }
  if (policyChanged || backendChanged) {
    if (typeof autonomy !== 'undefined') autonomy?.touch();
    if (typeof reflection !== 'undefined') reflection?.cancel();
    settingsRequests.cancel(); agent.cancel(); requests.cancel();
    brain.cancel(); decisionBrain.cancel();
  }
  if (['gamingMode', 'privacy'].some(changes) || backendChanged) memoryRequests.cancel();
  if (['gamingMode', 'privacy', 'systemAccess', 'screenAwareness'].some(changes) || backendChanged) {
    brain.reset({ keepRecent: !revokedRecall && !['systemAccess', 'screenAwareness', 'codexExecutable'].some(changes) });
  }
  if (patch.gamingMode === true || patch.screenAwareness === false) { walkthroughs.stop(); guide.clear('paused'); }
  if (patch.gamingMode === true && !['wake', 'commands'].includes(speech.current?.mode)) speech.cancel();
  if (patch.gamingMode === true
      || ['muted', 'volume', 'ttsEnabled', 'speakTypedReplies', 'proactiveVoice', 'ttsEngine', 'ttsPython', 'ttsModel', 'ttsReference', 'ttsReferenceText', 'ttsDevice'].some(changes)) tts.cancel();
  if (['ttsEnabled', 'ttsEngine', 'ttsPython', 'ttsModel', 'ttsReference', 'ttsReferenceText'].some(changes) || patch.muted === true) tts.close();
  if (patch.privacy) patch = { ...patch, privacy: nextPrivacy };
  config.save(patch);
  if (patch.gamingMode === false) reminders?.flush();
  if (backendChanged || patch.gamingMode === true || patch.visible === false ||
      [patch.interestsEnabled, patch.cognitiveEnabled, patch.agentEnabled].includes(false)) interestCollaboration.cancel();
  if (speech.current?.checkIn && (patch.muted === true || patch.volume === 0 ||
      [patch.checkInReplies, patch.proactiveVoice, patch.proactiveEnabled, patch.ttsEnabled].includes(false))) {
    speech.cancel(); endVoiceSession();
  }
  if (patch.wakeWordEnabled === false) { speech.cancel(); endVoiceSession(); }
  if (changes('wakeWordEnabled')) syncCommands();
  if (Object.hasOwn(patch, 'displayId')) fitOverlay();
  pcContext.eventSnapshot(); // discard event fields when permissions are revoked
  if (!config.load().windowTracking) {
    windowWatch?.stop(); windowWatch = null; lastWindows = null;
    overlay?.webContents.send('windows:update', { fg: null, wins: [] });
  } else if (overlay) watchWindows();
  if (memoryStore) memoryStore.prune();
  goalStore?.prune();
  const cfg = rendererConfig();
  overlay?.webContents.send('stella:config', cfg);
  rebuildTray();
  return cfg;
}

function settingsState() {
  return { config: { ...rendererConfig(), privacy: permissions(config.load().privacy) },
    initiative: initiativeTrial.status(),
    runtime: runtime(), integration: codexEvents.snapshot(),
    project: goals().projects.selected(),
    reminders: (() => { try { return reminderRows(reminderStore, resolveLang(config.load().lang)); } catch { return []; } })(),
    startup: app.getLoginItemSettings(loginItemOptions()).openAtLogin,
    displays: screen.getAllDisplays().map(d => ({ id: d.id, width: d.size.width, height: d.size.height })) };
}

function rebuildTray() {
  tray?.setToolTip(config.load().gamingMode ? 'Stella — paused · right-click to resume' : 'Stella — control room');
  settingsRoom?.update();
}

function openSettings() { settingsRoom?.open(); }

function startInitiativeTrial() {
  if (!initiativeTrial.start()) return 'There is already a quiet trial to review.';
  autonomy.touch();
  if (speech.current?.checkIn || checkInDeadline > Date.now()) {
    if (speech.current?.checkIn) { speech.cancel(); endVoiceSession(); }
    checkInDeadline = 0; tts.cancel();
  }
  settingsRoom?.update();
  return 'Quiet trial started for 24 hours. Check-ins stay quiet until you choose to resume them.';
}

function initiativeCommand(text) {
  const input = text.trim().replace(/[.!?]+$/, '');
  const match = /^\/companion trial(?:\s+(.*))?$/i.exec(input);
  const report = /^(?:show (?:me )?|review )?(?:the |my )?quiet trial(?: report)?$/i.test(input);
  const natural = /^start (?:the |a )?quiet trial$/i.test(input) ? 'start'
    : /^end (?:the )?quiet trial$/i.test(input) ? 'end' : /^resume (?:my |your )?check-ins$/i.test(input) ? 'resume' : null;
  if (!match && !report && !natural) return null;
  const action = (match?.[1] || natural || 'report').trim().toLowerCase();
  const response = text => ({ handled: true, text });
  if (action === 'start') return response(startInitiativeTrial());
  if (action === 'end') {
    if (!initiativeTrial.end()) return response('There is no quiet trial collecting decisions.');
    autonomy.touch(); settingsRoom?.update();
    return response('The trial is ready to review. Check-ins are still quiet.');
  }
  if (action === 'resume') {
    if (!initiativeTrial.resume()) return response('Check-ins are already following your normal settings.');
    autonomy.touch(); settingsRoom?.update();
    return response('Check-ins are following your normal settings again.');
  }
  const rating = /^rate\s+#?(\d+)\s+(welcome|bad-timing|repetitive)$/.exec(action);
  if (rating) return response(initiativeTrial.rate(Number(rating[1]), rating[2])
    ? 'Feedback saved.' : 'I couldn’t find a rateable check-in with that number.');
  const page = /^report(?:\s+before\s+#?(\d+))?$/.exec(action);
  if (!page) return response('Use /companion trial report, start, end, resume, or rate <number> <welcome|bad-timing|repetitive>.');
  const { startedAt, phase, endsAt } = initiativeTrial.status();
  if (startedAt === null) return response('No quiet trial yet. Use /companion trial start.');
  const summary = initiativeTrial.summary();
  const rows = initiativeTrial.decisions(page[1] ? Number(page[1]) : undefined);
  const counts = summary.map(row => `${row.count} ${row.outcome}`).join(', ');
  const calls = summary.reduce((total, row) => total + row.calls, 0);
  const latency = calls ? Math.round(summary.reduce((total, row) => total + (row.average_latency || 0) * row.calls, 0) / calls) : 0;
  const status = phase === 'running' ? `Collecting until ${new Date(endsAt).toLocaleString()}.`
    : phase === 'review' ? 'Ready for review. Check-ins are quiet.' : 'Check-ins have resumed.';
  return response([
    status, counts ? `${counts}. ${calls} model calls${calls ? `, about ${(latency / 1000).toFixed(1)} seconds per evaluated opportunity` : ''}.`
      : 'No check-in opportunities recorded yet.',
    ...rows.map(row => `#${row.id} · ${new Date(row.at).toLocaleString()} · ${row.outcome}${row.feedback ? ` · ${row.feedback}` : ''}\n${row.message ? `“${row.message}”\n` : ''}${row.reason}`),
    ...(rows.length ? ['Rate an entry with /companion trial rate <number> welcome, bad-timing, or repetitive.'] : []),
    ...(rows.length === 8 ? [`Older entries: /companion trial report before ${rows.at(-1).id}`] : []),
  ].join('\n\n'));
}

async function projectCommand(text) {
  if (projectRouting || brain.busy || actions.busy || chats.size)
    return { handled: true, text: 'Finish or stop the current request before changing project context.' };
  projectRouting = true;
  try {
    autonomy.touch();
    const previousScope = goals().projects.scope();
    const result = await goals().projects.route(text);
    groundedCuriosity.sync();
    if (goals().projects.scope() !== previousScope) actions.context?.clear();
    brain.reset({ keepRecent: goals().projects.scope() === previousScope && !/^\/project\s+(?:forget-note|delete)\b/i.test(text) });
    settingsRoom?.update();
    return result;
  } finally { projectRouting = false; }
}

async function settingsAction(name, value) {
  switch (name) {
    case 'reminder-cancel': case 'reminder-move': {
      if (!reminderStore) return 'Reminders are unavailable right now.';
      let message;
      if (name === 'reminder-cancel') message = reminderStore.cancel(value) ? 'Reminder cancelled.' : 'That reminder is already gone.';
      else { moveReminder(reminderStore, value); message = 'Reminder moved.'; }
      settingsRoom?.update(); return message;
    }
    case 'gaming': await setGamingMode(value); break;
    case 'visibility': toggleVisible(value); break;
    case 'startup': app.setLoginItemSettings({ ...loginItemOptions(), openAtLogin: value }); break;
    case 'voice-preview': {
      if (!config.load().ttsEnabled || config.load().muted) return 'Enable spoken replies and unmute Stella to preview her voice.';
      if (!overlay || overlay.isDestroyed() || !overlay.isVisible()) return 'Bring Stella back to preview her voice.';
      overlay.webContents.send('tts:state', { type: 'preview', mood: deliveryStyle(value),
        text: "There you are, sweetheart. Come here for a second. I have something to show you." });
      return 'Preparing her voice. The first preview needs a little time to warm up.';
    }
    case 'sounds-folder': fs.mkdirSync(userSoundsDir(), { recursive: true }); {
      const error = await shell.openPath(userSoundsDir()); if (error) throw Error(error); break;
    }
    case 'memory-export': return (await personal.route('/memory export')).text;
    case 'memory-delete': {
      autonomy.touch(); const result = await personal.route('/memory delete-all');
      brain.reset({ keepRecent: result.text !== 'All personal memories deleted.' }); return result.text;
    }
    case 'remember-chat': {
      if (config.load().rememberRecentChat === value) break;
      brain.cancel(); brain.reset({ keepRecent: true });
      recentConversation()?.clear();
      updateConfig({ rememberRecentChat: value });
      break;
    }
    case 'clear-recent-chat': {
      if (!await confirmMemory('Clear recent conversations?', 'This removes the recent chat text Stella can use to continue voice and text conversations.')) return 'Clear cancelled.';
      brain.cancel(); brain.reset({ keepRecent: true });
      recentConversation()?.clear();
      return 'Recent conversations cleared.';
    }
    case 'memory-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing memory.'); sendCommand('memory'); break;
    case 'interests-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing interests.'); sendCommand('interests'); break;
    case 'reviews-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing your day.'); sendCommand('reviews'); break;
    case 'curiosity-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing questions.'); sendCommand('curiosity'); break;
    case 'routines-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing routines.'); sendCommand('routines'); break;
    case 'initiative-start': return startInitiativeTrial();
    case 'initiative-open': if (config.load().gamingMode) throw Error('Resume Stella before reviewing check-ins.'); sendCommand('initiative'); break;
    case 'initiative-resume': return initiativeCommand('/companion trial resume').text;
    case 'project-choose': return (await foreground.run(() => projectCommand('/project choose'))).text;
    case 'project-off': return (await foreground.run(() => projectCommand('/project off'))).text;
    case 'refresh': return runtime().currentSource ? 'Current local source is loaded.' : 'Local changes found. Restart Stella to load them.';
    case 'restart': app.relaunch(); app.quit(); break;
    case 'quit': app.quit(); break;
  }
}

// Run from a clone (`npm start`), electron.exe alone would open the default Electron app at login:
// it needs the project folder as argument.
function loginItemOptions() {
  return app.isPackaged ? {} : { path: process.execPath, args: [ROOT] };
}

function createTray() {
  const icon = nativeImage.createFromPath(path.join(ROOT, 'assets', 'icons', 'stella.ico'));
  tray = new Tray(icon);
  tray.setToolTip('Stella — local only');
  tray.on('click', openSettings);
  tray.on('right-click', openSettings);
  rebuildTray();
}

function registerIpc() {
  const speechCaller = event => event.sender === overlay?.webContents;
  ipcMain.on('companion:state', (event, state) => { if (speechCaller(event)) {
      if (state?.chatOpen !== undefined && state.chatOpen !== presentation.chatOpen) {
        autonomy.touch(); if (state.voiceActive === true) tts.warm();
      }
      presentation = personalityContext(state);
    } });
  ipcMain.on('companion:event', (event, reason) => { if (speechCaller(event) && reason === 'chat-open') autonomy.touch(); });
  ipcMain.on('companion:body-result', (event, result) => {
    if (speechCaller(event) && typeof result?.id === 'string') bodyJobs.get(result.id)?.({ result: String(result.result || '').slice(0, 600) });
  });
  ipcMain.handle('tts:speak', (event, request) => speechCaller(event) ? tts.speak(request) : {ok:false,error:'Voice unavailable.'});
  ipcMain.on('tts:cancel', event => { if (speechCaller(event)) tts.cancel(false); });
  // Reminder cards: only the overlay may act on them (checked again in ReminderController).
  ipcMain.handle('reminder:action', (event, id, action, firedDue, minutes) =>
    reminders ? reminders.ipcAction(event.sender, id, action, firedDue, minutes) : { ok: false, error: 'Reminders are unavailable.' });
  ipcMain.on('reminder:shown', (event, id, firedDue) => { reminders?.shown(event.sender, id, firedDue); });
  ipcMain.on('reminder:ready', event => { if (speechCaller(event)) reminders?.setReady(true); });
  ipcMain.handle('speech:start', (event, request) => {
    if (!speechCaller(event)) return { ok: false, error: 'speech-unavailable' };
    if (request?.checkIn === true) {
      const cfg = config.load();
      if (request.mode !== 'conversation' || !sessionAvailable || fullscreenState.active || cfg.gamingMode ||
          !cfg.checkInReplies || !cfg.proactiveVoice || !cfg.proactiveEnabled || !cfg.ttsEnabled || cfg.muted || cfg.volume === 0 ||
          Date.now() >= checkInDeadline) return { ok: false, error: 'speech-paused' };
    }
    // Commands-only listening runs under her guide lines: it neither interrupts her nor counts as user activity.
    if (request?.mode !== 'commands') { if (request?.checkIn !== true) autonomy.touch(); tts.cancel(); }
    const result = speech.start(request);
    if (result.ok && request?.checkIn === true) checkInDeadline = 0;
    return result;
  });
  ipcMain.handle('wake:enabled', (event, enabled) => {
    if (!speechCaller(event) || typeof enabled !== 'boolean') throw Error('Invalid wake-word preference.');
    return updateConfig({ wakeWordEnabled: enabled });
  });
  ipcMain.on('wake:end-session', event => { if (speechCaller(event)) endVoiceSession(); });
  ipcMain.handle('speech:commands-state', event => ({ on: speechCaller(event) ? speech.commandsReady() : false }));
  ipcMain.handle('speech:stop', (event, request) => {
    if (!speechCaller(event)) return { ok: false, error: 'speech-unavailable' };
    return speech.stop(request?.id);
  });
  ipcMain.on('speech:audio', (event, request) => { if(speechCaller(event))speech.audio(request); });
  ipcMain.handle('speech:conversation', (event, request) => speechCaller(event) ? speech.conversation(request?.id) : {ok:false,error:'speech-unavailable'});
  ipcMain.on('speech:reset', (event, request) => {
    if (speechCaller(event)) speech.resetUtterance(request?.id, request?.listening !== false,
      Number.isSafeInteger(request?.preRollMs) ? request.preRollMs : undefined);
  });
  ipcMain.on('speech:cancel', (event, request) => {
    if (speechCaller(event) && request?.id === speech.current?.id) speech.cancel();
  });
  ipcMain.handle('fullscreen:state', event => {
    if (event.sender !== overlay?.webContents) throw Error('Overlay required.');
    return fullscreenState;
  });
  ipcMain.on('fullscreen:rendered', (event, state) => {
    if (event.sender !== overlay?.webContents || state?.revision !== fullscreenState.revision
        || state.hidden !== fullscreenState.active) return;
    clearTimeout(fullscreenHideTimer);
    if (state.hidden && !voiceSession) overlay.hide();
    overlay.webContents.setBackgroundThrottling(!config.load().wakeWordEnabled && !voiceSession && !commandsOn);
  });
  ipcMain.handle('runtime:info', () => runtime());
  ipcMain.handle('personal:route', async (event, text, id, conversation, commandsOnly = false, replyTo, conversationId) => foreground.run(async () => {
    try {
      if (event.sender !== overlay?.webContents) throw Error('Overlay required.');
      if (typeof text !== 'string' || text.length > 12000) throw Error('Invalid message.');
      const reminderReply = reminderStore && routeReminderCommand(text, reminderStore, resolveLang(config.load().lang));
      if (reminderReply) return reminderReply;
      // A running walkthrough keeps the guide layer: a command runs locally, anything else pauses it until answered; only "stop" or a new walkthrough ends it.
      const walkReply = walkthroughs.route(text);
      if (walkReply) return walkReply;
      // A new request leaves an explanation drawing up (asking about it must not erase it); see GuideSession's lifetime.
      if (projectRouting) return { handled: true, text: 'Finish choosing your project before sending a request.' };
      const trialReply = initiativeCommand(text);
      if (trialReply) return trialReply;
      const explanation = autonomy.explain(text, replyTo);
      if (explanation) return explanation;
      const inquiryAnchor = autonomy.state.lastInquiry;
      const interestReply = autonomy.respond(text, commandsOnly ? undefined : replyTo);
      autonomy.touch();
      if (interestReply?.pursuitFeedback) { brain.reset({ keepRecent: true }); return interestReply; }
      const topicPreference = await routeTopicPreference(text);
      if (topicPreference) return topicPreference;
      const collaboration = await interestCollaboration.route(text, { conversation: conversationId, turn: id,
        interestId: interestReply?.buildInterestId, commandsOnly, onStart: () => speech.promoteCheckIn(conversationId),
        onBusy: () => autonomy.defer(BUSY_PAUSE),
        projectSelected: () => permissions(config.load().privacy).memoryEnabled && Boolean(goals().projects.selected()) });
      if (collaboration) return collaboration;
      const routineCommand = await goals().routines.route(text, updateConfig);
      if (routineCommand) { brain.reset(); return routineCommand; }
      if (goals().routines.invocation(text)) return { handled: false };
      const feedbackCommand = groundedCuriosity.route(text);
      if (feedbackCommand) { if (groundedCuriosity.quietFeedback()) autonomy.defer(60); brain.reset({ keepRecent: true }); return feedbackCommand; }
      const anchored = Boolean(projectFeedbackAnchor && projectFeedbackAnchor.scope === goals().projects.scope()
        && Date.now() - projectFeedbackAnchor.at >= 0 && Date.now() - projectFeedbackAnchor.at < 10 * 60000)
        || Boolean(inquiryAnchor && Date.now() - inquiryAnchor.at >= 0 && Date.now() - inquiryAnchor.at < 10 * 60000
          && curiosity.list(100).some(row => row.id === inquiryAnchor.id && row.subject === inquiryAnchor.subject
            && row.evidence_revision === inquiryAnchor.revision && row.scope_id === goals().projects.scope()));
      const feedback = groundedCuriosity.recordFeedback(text, { anchored });
      if (['unhelpful', 'repetitive'].includes(feedback)) autonomy.defer(60);
      if (interestReply) { brain.reset({ keepRecent: true }); return interestReply; }
      const interestCommand = interests.route(text, updateConfig);
      if (interestCommand) { brain.reset({ keepRecent: !/^\/interests\s+clear$/i.test(text.trim()) }); return interestCommand; }
      if (/^\/project(?:\s|$)/i.test(text.trim())) {
        return await projectCommand(text);
      }
      const goalCommand = /^\/goals(?:\s|$)/i.test(text.trim()) ? goals().route(text) : null;
      if (goalCommand) { groundedCuriosity.sync(); brain.reset(); return goalCommand; }
      const continuityCommand = goals().continuity.route(text);
      if (continuityCommand) { brain.reset(); return continuityCommand; }
      const dailyReviewCommand = goals().reviews.route(text, updateConfig);
      if (dailyReviewCommand) { brain.reset(); return dailyReviewCommand; }
      const companion = /^\/companion(?:\s+(on|off|status))?$/i.exec(text.trim());
      if (companion) {
        const command = (companion[1] || 'status').toLowerCase();
        if (command !== 'status') updateConfig({ proactiveEnabled: command === 'on' });
        return { handled: true, text: JSON.stringify(autonomy.status(), null, 2) };
      }
      const curiosityCommand = /^\/curiosity(?:\s+(.*))?$/i.exec(text.trim());
      if (curiosityCommand) {
        const arg = (curiosityCommand[1] || 'status').trim().toLowerCase();
        if (arg === 'status') return { handled: true, text: JSON.stringify({ ...curiosity.status(), reflection: reflection.status() }, null, 2) };
        if (arg === 'list') return { handled: true, text: JSON.stringify(curiosity.list(), null, 2) };
        const history = /^history (\d+)$/.exec(arg);
        if (history) return { handled: true, text: JSON.stringify(curiosity.reviewContext(Number(history[1])), null, 2) };
        if (arg === 'on' || arg === 'off') { updateConfig({ cognitiveEnabled: arg === 'on' }); return { handled: true, text: 'Curiosity ' + arg }; }
        if (arg === 'clear') { reflection.cancel(); curiosity.clear(); return { handled: true, text: 'Curiosity journal cleared.' }; }
        const decision = /^(resolve|dismiss)\s+(\d+)$/.exec(arg);
        if (decision) return { handled: true, text: curiosity.update(Number(decision[2]), decision[1] === 'resolve' ? 'resolved' : 'dismissed') ? 'Question updated.' : 'Open question not found.' };
        return { handled: true, text: 'Use /curiosity status, list, history <id>, on|off, resolve <id>, dismiss <id>, or clear.' };
      }
      const preference = await settingsRequests.route(text);
      if (preference) return preference;
      if (/^\/(?:agent cancel|cancel)$/i.test(text.trim())) { brain.cancel(); decisionBrain.cancel(); requests.cancel(); memoryRequests.cancel(); }
      const result = await agent.route(text.trim());
      if (result !== null) return { handled: true, text: result };
      // Explicit slash commands remain available offline; natural language goes
      // straight to the single Codex tool loop.
      const simpleMemory = /^(?:forget\s+#?\d+\s*[.!]?$|edit memory\s+#?\d+\s*:|recall\s+)/i.test(text.trim())
        || (/^(?:remember(?: that)?|recuerda(?: que)?)\s+/i.test(text.trim())
          && !/\b(?:forget|remove|delete|edit|change|instead|olvida|borra|cambia)\b|[?]/i.test(text));
      if (/^\/(?:memory|privacy|context)(?:\s|$)/i.test(text.trim())
          || (simpleMemory && (commandsOnly === true || /^(?:forget\s+#?\d+\s*[.!]?$|edit memory\s+#?\d+\s*:|recall\s+)/i.test(text.trim())))) {
        const local = await personal.route(text);
        if (local.handled) brain.reset({ keepRecent: !/^(?:All personal memories deleted\.|Forgot memory #|Updated memory #)/.test(local.text) });
        return local;
      }
      if (!commandsOnly) {
        const direct = actions.routeDirect(text, id);
        if (direct) return await direct;
      }
      return { handled: false };
    }
    catch (err) { return { handled: true, text: `Local assistant unavailable: ${err.message}` }; }
  }).then(result => walkthroughs.afterRoute(result, commandsOnly === true), error => { walkthroughs.answered(); throw error; }));
  ipcMain.handle('task:openResult', async (_event, ref) => {
    try { if (typeof ref!=='string'||!/^[a-f0-9]{16}$/.test(ref)) throw Error('Invalid result.'); return {ok:true,...await actions.openResult(ref)}; }
    catch(error) { return {ok:false,error:error.message}; }
  });
  ipcMain.handle('integration:status', () => codexEvents.snapshot());
  ipcMain.on('overlay:interactive', (event, on, near = true) => {
    if (!speechCaller(event) || typeof on !== 'boolean' || !overlay || overlay.isDestroyed()) return;
    const ignore = ((fullscreenState.active || config.load().gamingMode) && !voiceSession) || !on;
    if (!ignore && !overlay.isFocusable()) setOverlayFocusable(true);
    setOverlayIgnore(ignore, near !== false);
  });
  ipcMain.handle('overlay:cursor', () => {
    const p = screen.getCursorScreenPoint();
    const b = overlay.getBounds();
    return { x: p.x - b.x, y: p.y - b.y, inside: p.x >= b.x && p.y >= b.y && p.x < b.x + b.width && p.y < b.y + b.height };
  });
  ipcMain.handle('config:get', () => rendererConfig());
  const openLink = createLinkOpener({ publicUrl, openUrl: (url, browser) => desktop.openUrl(url, browser) });
  ipcMain.handle('link:open', (event, url) => {
    if (event.sender !== overlay?.webContents) throw Error('Overlay required.');
    return openLink(url);
  });
  ipcMain.handle('config:set', (event, patch) => {
    if (event.sender !== overlay?.webContents) throw Error('Overlay required.');
    return updateConfig(DEV || smokeTest ? patch : overlayPatch(patch));
  });
  ipcMain.handle('demo:window', (_e, open) => demoWindow(open));
  // right-clicking her: the same menu as the tray icon (which Windows often hides behind the ^ by the clock)
  ipcMain.on('menu:open', openSettings);
  ipcMain.handle('windows:get', () => lastWindows);
  ipcMain.handle('chat:status', async event => {
    if (event.sender !== overlay?.webContents) throw Error('Overlay required.');
    return { ...await brain.status(), version: VERSION };
  });
  ipcMain.handle('chat:send', async (event, request) => foreground.run(async () => {
    if (event.sender !== overlay?.webContents) return { ok: false, error: 'Overlay required.' };
    autonomy.touch();
    const { id, messages } = request || {};
    const current = messages?.at(-1);
    if (!Number.isSafeInteger(id) || current?.role !== 'user' || typeof current.content !== 'string') return { ok: false, error: 'Invalid chat request.' };
    if (projectRouting) return { ok: false, error: 'Finish choosing your project before sending a request.' };
    if (chats.size || brain.busy || actions.busy) return { ok: false, error: 'One Stella request at a time.' };
    if (config.load().speakTypedReplies && tts.allowed()) tts.warm();
    const abort = new AbortController();
    let finish;
    const done = new Promise(resolve => { finish = resolve; });
    const stop = () => brain.cancel();
    abort.signal.addEventListener('abort', stop, { once: true });
    chats.set(id, { abort, done });
    const feedbackAnchorAtStart = projectFeedbackAnchor;
    try {
      const cfg = agentConfig();
      const privacy = permissions(cfg.privacy);
      const voice = request.mode === 'voice' && voiceSession;
      let delivery;
      const onDelivery = cfg.ttsEnabled && (voice || cfg.speakTypedReplies) ? style => {
        delivery = style;
        overlay?.webContents.send('chat:delta', { id, text: '', delivery });
      } : undefined;
      let statedMemory;
      if (!cfg.gamingMode && privacy.memoryEnabled && privacy.memoryLearn) {
        try { statedMemory = memory().learn(current.content).facts; }
        catch { console.error('[stella] Could not save stated personal details.'); }
      }
      const text = await brain.chat(current.content,
        text => overlay?.webContents.send('chat:delta', { id, text }),
        text => overlay?.webContents.send('task:progress', { id, text }), { voice, statedMemory, onDelivery, turn: id });
      if (projectFeedbackAnchor === feedbackAnchorAtStart) projectFeedbackAnchor = null;
      return { ok: true, text, closeViaTools: true, delivery };
    } catch (error) { projectFeedbackAnchor = null; return { ok: false, error: abort.signal.aborted ? 'stopped' : error.message }; }
    finally { abort.signal.removeEventListener('abort', stop); chats.delete(id); finish(); }
  }).finally(() => walkthroughs.answered()));
  ipcMain.on('chat:stop', (event, id) => {
    if (event.sender !== overlay?.webContents) return;
    interestCollaboration.cancel(id);
    chats.get(id)?.abort.abort(); brain.cancel(); decisionBrain.cancel(); walkthroughs.chatStopped(id);
    settingsRequests.cancel(); agent.cancel(); requests.cancel(); memoryRequests.cancel();
  });
  // closing an app you asked her to close, once you've clicked to confirm (apps.js)
  const appInfo = (app) => app && { name: app.process, label: app.label };
  ipcMain.handle('apps:list', async () => config.load().desktopActions && !config.load().gamingMode
    ? (await apps.list().catch(() => [])).map(appInfo) : []);
  ipcMain.handle('apps:find', async (_e, wanted) => config.load().desktopActions && !config.load().gamingMode
    ? appInfo(await apps.find(wanted).catch(() => null)) : null);
  ipcMain.handle('apps:close', closeApp);
  // typing to her: the overlay takes the keyboard while the chat is open, and gives it back after
  ipcMain.on('overlay:focus', (event, on) => {
    if (!speechCaller(event)) return;
    autonomy.touch();
    if (!overlay) return;
    if ((fullscreenState.active || config.load().gamingMode) && !voiceSession) return;
    if (on === true) { setOverlayFocusable(true); overlay.focus(); }
    else if (on === false) overlay.blur();
  });
  // her report card's copy button: a picture of that part of the overlay, on the clipboard
  ipcMain.handle('panel:copy', async (_e, rect) => {
    const image = await overlay.webContents.capturePage(rect);
    if (image.isEmpty()) return false;
    const png = new Blob([image.toPNG()], { type: 'image/png' });
    await clipboard.write([new ClipboardItem({ 'image/png': png })]);
    return true;
  });
  ipcMain.handle('sounds:list', () => {
    try {
      return fs.readdirSync(userSoundsDir())
        .filter((f) => SOUND_EXT.test(f))
        .map((f) => ({ name: f.replace(SOUND_EXT, '').toLowerCase(), url: `stella://usersounds/${encodeURIComponent(f)}` }));
    } catch {
      return [];
    }
  });
}

// Only in --dev: lets scripts drive the overlay and grab frames of it (no desktop content, just our window).
const testWins = new Map(); // name -> test window

async function debugHandler(route, body) {
  if (!DEV) throw new Error('debug routes need --dev');
  if (route === 'command') {
    sendCommand(body.name, body);
    return { ok: true };
  }
  if (route === 'reload') {
    overlay.webContents.reloadIgnoringCache();
    return { ok: true };
  }
  if (route === 'testwin') {
    // plain windows to sit on, opened without stealing focus, by name (`id`, default "main");
    // each one opened goes in front of the others. { open: false } without an id closes them all.
    const id = body.id ?? 'main';
    if (!body.open && body.id === undefined) {
      for (const win of testWins.values()) win.destroy();
      testWins.clear();
      return { ok: true };
    }
    testWins.get(id)?.destroy();
    testWins.delete(id);
    if (body.open) {
      const b = overlay.getBounds();
      const win = new BrowserWindow({
        x: b.x + (body.x ?? 300), y: b.y + (body.y ?? 380), width: body.w ?? 720, height: body.h ?? 380,
        show: false, alwaysOnTop: true, title: `Stella test window ${id}`, backgroundColor: '#1b1726',
      });
      win.loadURL('data:text/html,<body style="background:%231b1726"></body>');
      win.showInactive();
      testWins.set(id, win);
    }
    return { ok: true };
  }
  if (route === 'movewin' && testWins.has(body.id ?? 'main')) {
    const win = testWins.get(body.id ?? 'main');
    const [x, y] = win.getPosition();
    win.setPosition(x + (body.dx || 0), y + (body.dy || 0));
    return { ok: true };
  }
  if (route === 'mouse') {
    // the pointer moving over the overlay (css px), and clicking if asked, without touching the real one
    const at = { x: Math.round(body.x), y: Math.round(body.y) };
    overlay.webContents.sendInputEvent({ type: 'mouseMove', ...at });
    if (body.click) {
      overlay.webContents.sendInputEvent({ type: 'mouseDown', button: 'left', clickCount: 1, ...at });
      overlay.webContents.sendInputEvent({ type: 'mouseUp', button: 'left', clickCount: 1, ...at });
    }
    return { ok: true };
  }
  if (route === 'type') {
    // typing into the overlay (her chat), and Enter if asked
    if (body.text) await overlay.webContents.insertText(body.text);
    if (body.enter) {
      overlay.webContents.sendInputEvent({ type: 'keyDown', keyCode: 'Return' });
      overlay.webContents.sendInputEvent({ type: 'char', keyCode: 'Return' });
      overlay.webContents.sendInputEvent({ type: 'keyUp', keyCode: 'Return' });
    }
    return { ok: true };
  }
  if (route === 'capture') {
    const image = await overlay.webContents.capturePage();
    // installed, the app's own folder is read-only: its data folder instead
    const dir = path.join(app.isPackaged ? app.getPath('userData') : ROOT, 'captures');
    fs.mkdirSync(dir, { recursive: true });
    const file = path.join(dir, `${(body.name || 'frame').replace(/[^\w-]/g, '')}.png`);
    fs.writeFileSync(file, image.toPNG());
    return { ok: true, file };
  }
  throw new Error('unknown debug route');
}

function main() {
  if (!app.requestSingleInstanceLock()) {
    app.quit();
    return;
  }
  app.on('second-instance', () => {
    // Clicking the desktop shortcut after an update must not silently keep an
    // idle, stale copy alive. Active replies are left for the explicit tray restart.
    if (!runtime().currentSource && !chats.size) { app.relaunch(); app.quit(); }
    else sendCommand('status');
  });
  if (process.platform === 'win32') app.setAppUserModelId('stella.desktop');

  app.whenReady().then(() => {
    serveProtocol();
    settingsRoom = createSettingsWindow({ state: settingsState, patch: updateConfig, action: settingsAction });
    registerIpc();
    createOverlay();
    createTray();
    const topmostGuard = createTopmostGuard({
      shouldBeOnTop: () => Boolean(overlay && !overlay.isDestroyed() && overlay.isVisible() && !fullscreenState.active),
      isTopmost: () => require('./native-windows').isTopmost(overlay.getNativeWindowHandle()),
      // Toggle so Windows really re-applies HWND_TOPMOST; neither call activates her.
      restore: () => { overlay.setAlwaysOnTop(false); overlay.setAlwaysOnTop(true, 'screen-saver'); overlay.moveTop(); },
      raise: () => overlay.moveTop(),
    });
    if (process.platform === 'win32') fullscreenWatch = startFullscreenWatch({
      read: () => {
        if (smokeTest && !process.argv.includes('--fullscreen-only') && !process.argv.includes('--speech-only')) return null;
        const window = require('./native-windows').foregroundBounds();
        try { topmostGuard.check(window); } catch { /* never let the guard break fullscreen detection */ }
        return window;
      },
      display: () => screen.dipToScreenRect(null, targetDisplay().bounds),
      onChange: onFullscreen,
    });
    watchWindows();
    startReminders();
    // Existing OS events only; at most one in-memory snapshot with a 60-second TTL.
    for (const [event, reason] of [['resume', 'resume'], ['on-ac', 'power-change'], ['on-battery', 'power-change']]) {
      powerMonitor.on(event, () => { pcContext.onEvent(reason).catch(() => {}); autonomy.touch(); });
    }
    // Apply expiry on startup even if no memory is recalled this run.
    if (fs.existsSync(path.join(app.getPath('userData'), 'personal-memory.sqlite'))) {
      try { memory(); } catch { console.error('[stella] Personal memory unavailable; other features remain available.'); }
    }
    try {
      const history = recentConversation();
      if (config.load().rememberRecentChat === true) history?.prune();
      else history?.clear();
    } catch { console.error('[stella] Recent conversation storage unavailable.'); }
    if (fs.existsSync(path.join(app.getPath('userData'), 'companion-goals.sqlite'))) {
      try { goals(); } catch { console.error('[stella] Saved goals unavailable.'); }
    }
    let previousConnection;
    try { previousConnection = JSON.parse(fs.readFileSync(connectionFile(), 'utf8')); } catch {}
    integrationToken = /^[a-f0-9]{64}$/.test(previousConnection?.token || '') ? previousConnection.token : randomBytes(32).toString('hex');
    const bridge = createBridge({
      port: PORT,
      onDebug: DEV ? debugHandler : null,
      integrationToken,
      onIntegrationStatus: async ({ verifyContext } = {}) => {
        const status = { ...codexEvents.snapshot(), runtime: runtime(), gamingMode: config.load().gamingMode,
          visible: Boolean(overlay?.isVisible()), rendererReady: Boolean(overlay && !overlay.webContents.isLoading()),
          companion: autonomy.status(), cognition: { ...curiosity.status(), reflection: reflection.status() } };
        if (verifyContext) {
          // Fixed read-only diagnostic phrase. Never accept commands or prompt text
          // through the HTTP status endpoint, and never return app/window names.
          const previousTopic = personal.lastAppQuestion;
          try {
            const result = await personal.route('whats openned in my pc stella?');
            status.contextCheck = { handledLocally: Boolean(result.handled),
              reportsApps: /^(Open desktop apps|Running app processes|No matching apps)/.test(result.text || '') };
          } finally { personal.lastAppQuestion = previousTopic; }
        }
        return status;
      },
      onCodexEvent: (input) => {
        const first = !codexEvents.lastSeen;
        const event = codexEvents.accept(input);
        if (!event) return false;
        if (!config.load().gamingMode) {
          overlay?.webContents.send('integration:state', codexEvents.snapshot());
          overlay?.webContents.send('integration:event', event);
        }
        if (first && codexEvents.lastSeen) rebuildTray();
        return true;
      },
    });
    bridge.once('listening', () => {
      const target = connectionFile();
      fs.mkdirSync(path.dirname(target), { recursive: true });
      // Publish only after we own the port. A failed second launch must not replace it.
      fs.writeFileSync(target, JSON.stringify({ port: PORT, token: integrationToken }), { mode: 0o600 });
    });
    globalShortcut.register('Control+Alt+C', () => toggleVisible());
    reflection.schedule();
    const reflectionTimer = setInterval(() => {
      try { groundedCuriosity.sync(); } catch { /* Saved evidence remains optional. */ }
      reflection.schedule();
    }, 60000);
    reflectionTimer.unref(); app.once('before-quit', () => clearInterval(reflectionTimer));
    for (const event of ['suspend', 'resume', 'lock-screen', 'unlock-screen']) powerMonitor.on(event, () => {
      sessionAvailable = event === 'resume' || event === 'unlock-screen';
      autonomy.observeIdle(null); autonomy.touch(); reflection.cancel();
      if (!sessionAvailable) {
        walkthroughs.stop(); guide.clear('locked');
        brain.dropWarmClient();
        checkInDeadline = 0; tts.cancel();
        interestCollaboration.cancel();
        if (speech.current?.checkIn) { speech.cancel(); endVoiceSession(); }
        commandWindowUntil = 0;
      } else { reminderScheduler?.resume(); reminders?.redeliver(); } // held while locked: shown now, missed ones once
      syncCommands();
    });
    const presenceTimer = setInterval(() => {
      const cfg = config.load();
      autonomy.observeIdle(sessionAvailable && cfg.proactiveVoice && permissions(cfg.privacy).contextEvents
        ? powerMonitor.getSystemIdleTime() : null);
      try {
        groundedCuriosity.sync();
        const offered = goals().reviews.tick({
          available: initiativeTrial.status().phase === 'live' && autonomy.enabled() && !autonomy.busy && autonomy.canRun(),
          notify: text => {
            if (!sessionAvailable || !overlay || overlay.isDestroyed() || !autonomy.canRun()) return false;
            brain.history = [...brain.history, { role: 'assistant', content: text }].slice(-24);
            overlay.webContents.send('companion:conversation', text); return true;
          },
        });
        if (offered) autonomy.touch();
        else autonomy.run().catch(() => {});
      } catch { /* Review storage cannot stop ordinary companion conversations. */
        autonomy.run().catch(() => {});
      }
    }, 15000);
    presenceTimer.unref(); app.once('before-quit', () => clearInterval(presenceTimer));
    screen.on('display-metrics-changed', fitOverlay);
    screen.on('display-added', () => { fitOverlay(); rebuildTray(); });
    screen.on('display-removed', () => { fitOverlay(); rebuildTray(); });
  });

  app.on('before-quit', () => { autonomy.close(); reflection.close(); cognitiveBrain.cancel(); brain.cancel(); decisionBrain.cancel(); speech.cancel(true); tts.close(); agent.cancel(); requests.cancel(); memoryRequests.cancel(); for (const { abort } of chats.values()) abort.abort(); });
  app.on('will-quit', () => {
    globalShortcut.unregisterAll();
    windowWatch?.stop();
    fullscreenWatch?.stop();
    clearTimeout(fullscreenHideTimer);
    memoryStore?.close(); recentChatStore?.close(); goalStore?.close(); curiosity?.close();
    reminderScheduler?.stop(); reminderStore?.close();
  });
  app.on('window-all-closed', (e) => e.preventDefault());
}

main();
